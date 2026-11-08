// Tests of the powers of the dyadic kernel at their exact cases, through `check_pow` and
// `check_pown` of `tests.rs`, with the result that each case has to give in both directions.
//
// x^y for a finite x > 0 other than 1 and a finite y != 0 is an `f64` only in two families,
// which `exact` of `pow.rs` finds before the loop: (A) x = 2^e with an integer e y, and (B)
// x = r^(2^k) 2^(2^k er) for an odd r >= 3 with y = m / 2^k, for an odd m if k > 0, and
// r^m < 2^53; in both, x^y has to be in range. x^n for x = ±r 2^er with an odd r and n != 0
// is an `f64` exactly when x^n is in range and either r = 1, or n > 0 and r^n < 2^53. Each
// generator takes cases of a family, where both directions have to give the exact result,
// and arguments next to them, most of which give results that are not `f64`s, where the two
// directions have to differ. Each case also goes through `check_pow` or `check_pown`, which
// compare it with MPFR on 64-bit Linux and macOS.

use super::*;

// m 2^e if it is an `f64`, for m < 2^53: if m != 0 and its least and its top bit are in range.
fn value(m: u64, e: i64) -> Option<f64> {
    let top = e + 63 - i64::from(m.leading_zeros());
    if m != 0 && e >= -1074 && top <= 1023 {
        assert!(m < 1 << 53);
        // m and 2^e are `f64`s, and so is their product.
        Some(m as f64 * pow2(e))
    } else {
        None
    }
}

// `lo` and `hi` are the two roundings of `want`, the `f64` that the result is, or differ if
// `want` is `None`: a result that is not an `f64` lies strictly between them.
fn check_exact(what: &str, lo: f64, hi: f64, want: Option<f64>) {
    match want {
        Some(v) => check_rounding(what, lo, hi, "E", v),
        None => assert!(lo < hi, "{}: ({:e}, {:e}) are equal", what, lo, hi),
    }
}

// Checks x^y in both directions against `want`, as `check_exact` does, and with `check_pow`.
fn check_pow_is(x: f64, y: f64, want: Option<f64>) {
    let (lo, hi) = (pow(x, y, false), pow(x, y, true));
    check_exact(&format!("pow({:e}, {:e})", x, y), lo, hi, want);
    check_pow(x, y);
}

// The arguments one ulp from the cases of (A) are checked at every `STRIDE`-th case only, so
// that the test takes a few seconds.
const STRIDE: usize = 7;

// (A): x = 2^e for every e in [-1074, 1023] other than 0, and y = j / 2^k for each k up to
// the number of trailing zeros of e and up to 10, an odd j if k > 0, and |j| up to
// 1075 / |e / 2^k| + 1, so that e y = (e / 2^k) j is an integer, in range or just out of it.
// x^y = 2^(e y) is an `f64` when e y is in [-1074, 1023]. Next to them: y one bit finer, with
// k one more than the trailing zeros of e, and |j| up to twice as far, where e y is half an
// odd integer. At every `STRIDE`-th case also: y ± 1 ulp, where e y is not an integer, as
// |y| < 2^11 and so the odd part of y ± 1 ulp is at 2^-42 or below; and x ± 1 ulp, whose odd
// part for a normal x is 2^52 + 1, 2^53 - 1 or, below 2^-1022, 2^52 - 1, none of them a
// square, so that x^y is an `f64` only for y = 1, while for a subnormal x they are checked by
// `check_pow` only.
#[test]
fn powers_of_two() {
    check_pow_is(4.0, 1.5, Some(8.0));
    check_pow_is(pow2(-1024), pow2(-10), Some(0.5));
    let mut case = 0;
    for e in (-1074..=1023i64).filter(|&e| e != 0) {
        let x = pow2(e);
        let tz = e.trailing_zeros();
        for k in 0..=tz.min(10) + 1 {
            // e / 2^k, and for the finer y, e / 2^(k - 1), which is odd.
            let f = e >> k.min(tz);
            let (finer, jmax) = if k > tz {
                (true, 2 * (1075 / f.abs() + 1))
            } else {
                (false, 1075 / f.abs() + 1)
            };
            for j in (-jmax..=jmax).filter(|&j| j != 0 && (k == 0 || j % 2 != 0)) {
                // |j| < 2^12, so that y is exact.
                let y = j as f64 / f64::from(1u32 << k);
                let want = if finer { None } else { value(1, f * j) };
                check_pow_is(x, y, want);
                case += 1;
                if case % STRIDE != 0 {
                    continue;
                }
                for y in [next_down(y), next_up(y)] {
                    check_pow_is(x, y, None);
                }
                for x in [next_down(x), next_up(x)] {
                    if e >= -1022 {
                        check_pow_is(x, y, if y == 1.0 { Some(x) } else { None });
                    } else {
                        check_pow(x, y);
                    }
                }
            }
        }
    }
}

// r^p if it is below 2^53.
fn power(r: u64, p: u32) -> Option<u64> {
    u128::from(r)
        .checked_pow(p)
        .filter(|&q| q < 1 << 53)
        .map(|q| q as u64)
}

// The least and the greatest integer s with m 2^(s d) an `f64`, for 0 < m < 2^53 and d >= 1.
fn shifts(m: u64, d: i64) -> (i64, i64) {
    let bits = 64 - i64::from(m.leading_zeros());
    // ceil(-1074 / d) and floor((1024 - bits) / d), as 1024 - bits > 0.
    let (lo, hi) = (-(1074 / d), (1024 - bits) / d);
    assert!(value(m, lo * d).is_some() && value(m, (lo - 1) * d).is_none());
    assert!(value(m, hi * d).is_some() && value(m, (hi + 1) * d).is_none());
    (lo, hi)
}

// The greatest odd r with r^(2^k) < 2^53, for k from 0 to 5.
const GREATEST: [u64; 6] = [(1 << 53) - 1, 94_906_265, 9741, 97, 9, 3];

// (B): x = r^(2^k) 2^(2^k er) for k from 0 to 5, each odd r from 3 to 99 with r^(2^k) < 2^53
// and the greatest such odd r, and y = m / 2^k for m from 1 to 33, odd if k > 0, where
// x^y = r^m 2^(m er) is an `f64` if r^m < 2^53 and r^m 2^(m er) is in range. er is 0, the
// least and the greatest er for which x is an `f64`, and, between those, the least and the
// greatest er for which x^y is an `f64` and the integers next to them. With each case: x^-y,
// which is not an `f64`, as r^-m is not a dyadic number; y ± 1 ulp, where x^y is not an
// `f64`, as y <= 33 and so the odd part of y ± 1 ulp is at 2^-47 or below, which would make
// x a 2^47-th power of a dyadic number and its odd part r^(2^k), in [3, 2^53), a 2^47-th
// power of an integer; and x ± 1 ulp, checked by `check_pow` only.
#[test]
fn powers_of_odd_numbers() {
    check_pow_is(9.0, 0.5, Some(3.0));
    let (r32, r33) = (power(3, 32).unwrap(), power(3, 33).unwrap());
    check_pow_is(r32 as f64, 33.0 / 32.0, Some(r33 as f64));
    for (k, &g) in GREATEST.iter().enumerate() {
        let d = 1 << k;
        assert!(power(g, d).is_some() && power(g + 2, d).is_none());
        let rs = (3..=99).step_by(2).filter(|&r| r <= g);
        for r in rs.chain(Some(g).filter(|&g| g > 99)) {
            // r^(2^k) < 2^53, as r <= g.
            let big = power(r, d).unwrap();
            let (lo, hi) = shifts(big, i64::from(d));
            for m in (1..=33).filter(|m| k == 0 || m % 2 == 1) {
                let q = power(r, m);
                let mut ers = vec![0, lo, hi];
                if let Some(q) = q {
                    let (a, b) = shifts(q, i64::from(m));
                    ers.extend([a - 1, a, b, b + 1].iter().filter(|&&s| lo <= s && s <= hi));
                }
                ers.sort_unstable();
                ers.dedup();
                // m < 2^6, so that y is exact.
                let y = f64::from(m) / f64::from(d);
                for er in ers {
                    let x = value(big, er << k).unwrap();
                    let want = q.and_then(|q| value(q, er * i64::from(m)));
                    check_pow_is(x, y, want);
                    check_pow_is(x, -y, None);
                    for y in [next_down(y), next_up(y)] {
                        check_pow_is(x, y, None);
                    }
                    for x in [next_down(x), next_up(x)] {
                        check_pow(x, y);
                    }
                }
            }
        }
    }
}

// Checks x^n and (-x)^n in both directions against `want`, the `f64` that x^n is, if any, as
// `check_exact` does, with the sign (-1)^n for -x, and with `check_pown`.
fn check_pown_is(x: f64, n: i32, want: Option<f64>) {
    let odd = n % 2 != 0;
    for (x, want) in [(x, want), (-x, want.map(|v| if odd { -v } else { v }))] {
        let (lo, hi) = (pown(x, n, false), pown(x, n, true));
        check_exact(&format!("pown({:e}, {})", x, n), lo, hi, want);
        check_pown(x, n);
    }
}

// x^n and (-x)^n: (1) for x = 2^e and every e in [-1074, 1023], where x^n = 2^(e n) is an
// `f64` if e n is in [-1074, 1023], with n at the ends of that range and next to them, ±1, ±2,
// `i32::MIN` and `i32::MAX`; (2) for x = r 2^er, each odd r of (B), and for each n from 2 to
// 33 the greatest odd r with r^n < 2^53 and the odd number after it, with n from 1 to the
// first n with r^n >= 2^53, where x^n = r^n 2^(n er) is an `f64` if r^n < 2^53 and it is in
// range. er is as in (B), from x and x^n. Next to them: x^-n, which is not an `f64`, as r^-n
// is not a dyadic number.
#[test]
fn pown_exact() {
    for e in -1074..=1023 {
        let x = pow2(e);
        let mut ns = vec![1, -1, 2, -2, i32::MIN, i32::MAX];
        if e != 0 {
            // e n = s |e| for s = n sgn(e), which is in range for s in [lo, hi].
            let (lo, hi) = shifts(1, e.abs());
            for s in [lo - 1, lo, hi, hi + 1] {
                ns.push(i32::try_from(s * e.signum()).unwrap());
            }
        }
        for n in ns {
            check_pown_is(x, n, value(1, e * i64::from(n)));
        }
    }
    let mut rs: Vec<u64> = (3..=99).step_by(2).chain(GREATEST).collect();
    for n in 2..=33 {
        // From an estimate of 2^(53 / n), which is above 3.
        let mut r = (53.0 / f64::from(n)).exp2() as u64 | 1;
        while power(r, n).is_none() {
            r -= 2;
        }
        while power(r + 2, n).is_some() {
            r += 2;
        }
        rs.extend([r, r + 2]);
    }
    rs.sort_unstable();
    rs.dedup();
    for r in rs {
        let (lo, hi) = shifts(r, 1);
        for n in 1.. {
            let q = power(r, n);
            let mut ers = vec![0, lo, hi];
            if let Some(q) = q {
                let (a, b) = shifts(q, i64::from(n));
                ers.extend([a - 1, a, b, b + 1].iter().filter(|&&s| lo <= s && s <= hi));
            }
            ers.sort_unstable();
            ers.dedup();
            let m = i32::try_from(n).unwrap();
            for er in ers {
                let x = value(r, er).unwrap();
                check_pown_is(x, m, q.and_then(|q| value(q, er * i64::from(n))));
                check_pown_is(x, -m, None);
            }
            if q.is_none() {
                break;
            }
        }
    }
}
