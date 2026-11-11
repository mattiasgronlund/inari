// Tests of `exact_div`, `tiny_quotient` and `midpoint_quotient` at random arguments, against an
// integer oracle that does not use `Dyadic`. For finite nonzero y and x, |y| = Y 2^i and
// |x| = X 2^j with odd integers Y and X (`odd_parts`), so that y / x is a dyadic number exactly
// when X divides Y, and is then ±m 2^(i - j) with the odd m = Y / X <= Y < 2^53. Below 1 it is
// then an `f64` exactly when i - j >= -1074, and an odd multiple of 2^-1075, the midpoints that
// `midpoint_quotient` looks for, exactly when i - j = -1075.
//
// Each argument also goes through `same_map` of `src/dyadic/atan/tests.rs`, which compares the
// two functions with their `Dyadic` versions from before their `f64` tests. Where `exact_div`
// takes an argument, the tests count the false positives of the residual alone: the arguments
// at which `fma(q, x, -y)` is 0 for q = y / x rounded to nearest, while y / x is not an `f64`.
// They are the reason that `exact_div` scales y below 2^-968, and `exact_div_random` checks
// that they occur among its arguments.

use super::*;

// (Y, i) with |v| = Y 2^i and Y odd, for finite v != 0.
fn odd_parts(v: f64) -> (u64, i32) {
    let bits = v.abs().to_bits();
    // A subnormal |v| is bits 2^-1074, and a normal one (2^52 + its fraction) 2^(E - 1075) for
    // its biased exponent E.
    let (m, e) = if bits >> 52 == 0 {
        (bits, -1074)
    } else {
        (
            (bits & ((1 << 52) - 1)) | (1 << 52),
            (bits >> 52) as i32 - 1075,
        )
    };
    let t = m.trailing_zeros();
    (m >> t, e + t as i32)
}

// y / x if it is an `f64`, and `None` otherwise, for finite y != 0 and |y| < x.
fn quotient_if_f64(y: f64, x: f64) -> Option<f64> {
    let ((yo, i), (xo, j)) = (odd_parts(y), odd_parts(x));
    // Where X divides Y, y / x = (Y / X) 2^(i - j) < 1, so that i - j < 0. Y / X < 2^53 is
    // exact, and so is 2^(i - j) for i - j >= -1074, and then their product, an `f64`.
    if yo % xo == 0 && i - j >= -1074 {
        Some(((yo / xo) as f64 * pow2(i - j)).copysign(y))
    } else {
        None
    }
}

// The `f64` next to y / x toward zero, with the sign of y, if y / x is an odd multiple m 2^-1075
// of 2^-1075, midway between the `f64`s (m - 1) 2^-1075 and (m + 1) 2^-1075, and `None`
// otherwise, for finite y != 0 and x > 0.
fn midpoint_if_any(y: f64, x: f64) -> Option<f64> {
    let ((yo, i), (xo, j)) = (odd_parts(y), odd_parts(x));
    // m = Y / X < 2^53, so that (m - 1) 2^-1075 = ((m - 1) / 2) 2^-1074 is the `f64` with the
    // bits (m - 1) / 2, +0 for m = 1, and `copysign` gives it the sign of y.
    if yo % xo == 0 && i - j == -1075 {
        Some(f64::from_bits((yo / xo - 1) / 2).copysign(y))
    } else {
        None
    }
}

// Checks that `exact_div(y, x)` is y / x if that is an `f64`, and `None` otherwise, for finite
// y != 0 and |y| < x < 2^996. Returns whether (y, x) is a false positive of the residual alone:
// y / x is not an `f64`, and `fma(q, x, -y)` is 0 for q = y / x rounded to nearest.
fn check_exact_div(y: f64, x: f64) -> bool {
    let expected = quotient_if_f64(y, x);
    assert_eq!(
        exact_div(y, x).map(f64::to_bits),
        expected.map(f64::to_bits),
        "exact_div({:e}, {:e})",
        y,
        x
    );
    expected.is_none() && (y / x).mul_add(x, -y) == 0.0
}

// `same_map` at (y, x), for finite y != 0 and x > 0, and the checks of `tiny_quotient`,
// `midpoint_quotient` and `exact_div` against the oracle: `tiny_quotient` gives y / x if it is
// an `f64` below `TINY_HYP` in magnitude, which needs |y| < x, and `None` otherwise, and
// `midpoint_quotient` gives `midpoint_if_any`. For x < 2^996, below which the two functions
// call `exact_div`, `check_exact_div` runs at (y, x) for |y| < x, and at (2y, x), at which
// `midpoint_quotient` calls it, for |2y| < x. Returns whether the residual alone would have
// changed a result: whether (y, x) is a false positive below `TINY_HYP`, which
// `tiny_quotient` would then have given, and whether (2y, x) is one whose rounded quotient is
// below 2^-1021 with odd bits, at which `midpoint_quotient` would have given a midpoint.
fn check_rules(y: f64, x: f64) -> [bool; 2] {
    same_map(y, x);
    let tiny = if y.abs() < x {
        quotient_if_f64(y, x).filter(|q| q.abs() < TINY_HYP)
    } else {
        None
    };
    assert_eq!(
        tiny_quotient(y, x).map(f64::to_bits),
        tiny.map(f64::to_bits),
        "tiny_quotient({:e}, {:e})",
        y,
        x
    );
    assert_eq!(
        midpoint_quotient(y, x).map(f64::to_bits),
        midpoint_if_any(y, x).map(f64::to_bits),
        "midpoint_quotient({:e}, {:e})",
        y,
        x
    );
    let mut false_positives = [false; 2];
    if x < TWO_996 {
        if y.abs() < x {
            false_positives[0] = check_exact_div(y, x) && (y / x).abs() < TINY_HYP;
        }
        // 2y is exact for |y| < 2^1023, and +∞ above, which the test |2y| < x leaves out.
        let t = 2.0 * y;
        if t.abs() < x {
            let q = t / x;
            false_positives[1] =
                check_exact_div(t, x) && q.abs() < TWO_M1021 && q.to_bits() & 1 == 1;
        }
    }
    false_positives
}

// (y, x) with y / x = ±m 2^c for an odd m: x = X 2^f and y = ±m X 2^(c + f), for an odd X of
// bx bits, bx uniform in [1, 26], and an odd m of bm bits, bm uniform in [1, 53 - bx], so
// that m X < 2^53, and a random sign. c is eq - (bm - 1) for `Some(eq)`, which gives y / x the
// exponent eq, and -1075 for `None`, at which y / x is a midpoint between two `f64`s. f gives
// y the exponent e if `of_y`, and x otherwise. y and x are rounded as `times_pow2` rounds them,
// so that y / x is ±m 2^c where both are exact, as x is for f >= -1074 and y for
// c + f >= -1074.
fn dyadic_pair(rng: &mut Rng, eq: Option<i32>, of_y: bool, e: i32) -> (f64, f64) {
    let bx = uniform(rng, 1, 26);
    let bm = uniform(rng, 1, 53 - bx);
    let xo = odd(rng, bx as u32);
    let yo = xo * odd(rng, bm as u32);
    // The bits of m X, bm + bx - 1 or bm + bx.
    let by = 64 - yo.leading_zeros() as i32;
    let c = eq.map_or(-1075, |eq| eq - (bm - 1));
    let f = if of_y { e - c - by + 1 } else { e - bx + 1 };
    // X 2^-(bx - 1) and m X 2^-(by - 1) are exact, and in [1, 2).
    let x = times_pow2(xo as f64 / pow2(bx - 1), f + bx - 1);
    let y = random_sign(rng) * times_pow2(yo as f64 / pow2(by - 1), c + f + by - 1);
    (y, x)
}

// `check_rules` at 10^5 random (y, x) with 0 < |y| < 2^-968, at which `exact_div` scales y by
// 2^128, and |y| < x, a quarter of them of each of these kinds:
// - y log-uniform with an exponent in [-1074, -969] and a random sign, and x log-uniform with
//   an exponent 1 to 60 above that of y;
// - such a y with x log-uniform with an exponent in [-60, 9], at which 2y / x is subnormal for
//   some;
// - `dyadic_pair` at an x of exponent e uniform in [-1000, 9] and a y / x of exponent eq
//   uniform in [max(-1080, -1074 - e), min(-1, -970 - e)], so that y has an exponent in
//   [-1074, -969], eq + e or eq + e + 1, and y / x is an `f64` where y is exact and
//   eq - (bm - 1) >= -1074, and below 2^-1074 for eq < -1074;
// - `dyadic_pair` at a midpoint, y / x = m 2^-1075, at an x of exponent uniform in [1, 40],
//   where y is exact.
// Both kinds of false positives that `check_rules` counts occur, and so do quotients that
// `tiny_quotient` gives and midpoints. 1 in 16 of the arguments also go through `check2_fast`,
// which compares atan2 with its fast path and without it, and with MPFR on 64-bit Linux and
// macOS.
#[test]
fn exact_div_random() {
    let mut rng = Rng(103);
    // The false positives of each kind, the quotients that `tiny_quotient` gives, and the
    // midpoints.
    let mut counts = [0; 4];
    for n in 0..100_000 {
        let (y, x) = match n % 4 {
            0 => {
                let y = random_sign(&mut rng) * log_uniform(&mut rng, -1074, -969);
                let ey = exponent(y);
                (y, log_uniform(&mut rng, ey + 1, ey + 60))
            }
            1 => (
                random_sign(&mut rng) * log_uniform(&mut rng, -1074, -969),
                log_uniform(&mut rng, -60, 9),
            ),
            2 => {
                let e = uniform(&mut rng, -1000, 9);
                let eq = uniform(&mut rng, (-1074 - e).max(-1080), (-970 - e).min(-1));
                dyadic_pair(&mut rng, Some(eq), false, e)
            }
            _ => {
                let e = uniform(&mut rng, 1, 40);
                dyadic_pair(&mut rng, None, false, e)
            }
        };
        assert!(
            y != 0.0 && y.abs() < TWO_M968 && y.abs() < x,
            "({:e}, {:e})",
            y,
            x
        );
        let false_positives = check_rules(y, x);
        counts[0] += usize::from(false_positives[0]);
        counts[1] += usize::from(false_positives[1]);
        counts[2] += usize::from(tiny_quotient(y, x).is_some());
        counts[3] += usize::from(midpoint_quotient(y, x).is_some());
        if n % 16 == 0 {
            check2_fast(y, x);
        }
    }
    assert!(counts.iter().all(|&c| c > 0), "counts {counts:?}");
}

// `check_rules` at 10^5 random (y, x) in each of three sets, with random signs of y:
// - A: |y| = my 2^ey and x = mx 2^(ey - d), for an ey uniform in [-971, -965], around 2^-968,
//   below which `exact_div` scales y;
// - B: x = mx 2^ex and |y| = my 2^(ex + d), for an ex uniform in [993, 999], around 2^996,
//   from which the two functions divide with `Dyadic`s instead;
// - C: x = mx 2^ex for an ex uniform in [-10, 9], and |y| = x (my 2^eq), each product rounded
//   to nearest, for an eq uniform in [-1030, -1010], at which atan2 is subnormal.
// In A and B, d is uniform in [-28, -22] for half of them, around the 2^-25 of the first check
// of `tiny_quotient`, and in [-1025, -1019] for the other half, around the 2^-1021 of that of
// `midpoint_quotient`. my and mx are random in [1, 2), and for 1 in 8 of them one of the edges
// 1, next_up(1), 1.5 and next_down(2), as in `quotient_rules_same_map`. 1 in 4 of the arguments
// are from `dyadic_pair` at the same exponents instead, of y in A and of x in B and C, half of
// them with y / x of exponent d in A and B and eq in C, and half at midpoints. In each set
// each function gives a quotient at some arguments, A has |y| on both sides of 2^-968, and B
// has x on both sides of 2^996.
#[test]
fn exact_div_same_map() {
    let edges = [1.0, next_up(1.0), 1.5, next_down(2.0)];
    let mantissa = |rng: &mut Rng| {
        if rng.below(8) == 0 {
            edges[rng.below(4) as usize]
        } else {
            1.0 + rng.below(1 << 52) as f64 / (1u64 << 52) as f64
        }
    };
    let mut rng = Rng(996);
    for set in 0..3 {
        // The arguments at which each function gives a quotient, and those below and above
        // 2^-968 (|y|, in A) or 2^996 (x, in B).
        let mut counts = [0; 4];
        let mut n = 0;
        while n < 100_000 {
            let d = if set == 2 {
                uniform(&mut rng, -1030, -1010)
            } else if rng.below(2) == 0 {
                uniform(&mut rng, -28, -22)
            } else {
                uniform(&mut rng, -1025, -1019)
            };
            let pair = rng.below(4) == 0;
            let eq = if rng.below(2) == 0 { Some(d) } else { None };
            let e = uniform(&mut rng, [-971, 993, -10][set], [-965, 999, 9][set]);
            let (y, x) = if pair {
                dyadic_pair(&mut rng, eq, set == 0, e)
            } else {
                let (my, mx) = (mantissa(&mut rng), mantissa(&mut rng));
                let sign = random_sign(&mut rng);
                match set {
                    0 => (sign * my * pow2(e), times_pow2(mx, e - d)),
                    1 => (sign * times_pow2(my, e + d), mx * pow2(e)),
                    _ => {
                        let x = mx * pow2(e);
                        (sign * x * times_pow2(my, d), x)
                    }
                }
            };
            // Some midpoints of `dyadic_pair` in C have a y that rounds to 0, which the
            // functions do not take.
            if y == 0.0 {
                continue;
            }
            n += 1;
            let side = if set == 0 {
                y.abs() >= TWO_M968
            } else {
                x >= TWO_996
            };
            check_rules(y, x);
            counts[0] += usize::from(tiny_quotient(y, x).is_some());
            counts[1] += usize::from(midpoint_quotient(y, x).is_some());
            counts[2 + usize::from(side)] += 1;
        }
        assert!(
            counts[0] > 0 && counts[1] > 0 && (set == 2 || (counts[2] > 0 && counts[3] > 0)),
            "set {}: counts {:?}",
            ["A", "B", "C"][set],
            counts
        );
    }
}
