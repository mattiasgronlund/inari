// Tests of `pow_near` and `pown_near` at the midpoints between adjacent `f64`s, where an
// enclosure settles the rounding to nearest only if the midpoint is one of its bounds, so that
// the kernel has to find the tie, or compute it exactly, and round it to even, and at the `f64`s
// next to their arguments, whose powers are not midpoints.
//
// For an odd r >= 3 and an n >= 2 with r^n in [2^53, 2^54), r^n is odd, and the `f64`s next to
// it are the even r^n - 1 and r^n + 1. Rust converts an integer to the `f64` nearest to it,
// ties to even, so `(r^n as u64) as f64` is r^n rounded as `pow_near` has to round it, and
// shifting the three by 2^(k n) through their bits keeps them exact while they are normal. Below
// 2^-1021, the `f64`s are the j 2^-1074 for j <= 2^53, whose bits are j, so that
// (2j + 1) 2^-1075 is halfway between the `f64`s with the bits j and j + 1. The expected values
// come from these integers and `f64::from_bits`, not from the kernel.

use super::*;

// The number of bases r that `odd_bases` takes at random where there are more.
const LIMIT: u64 = 500;

// v 2^s for a normal v > 0, if it is normal, from the bits of v: then it is exact.
fn shifted(v: f64, s: i64) -> Option<f64> {
    let be = i64::try_from(v.to_bits() >> 52).unwrap() + s;
    if (1..=2046).contains(&be) {
        let f = v.to_bits() & ((1 << 52) - 1);
        Some(f64::from_bits(f | u64::try_from(be).unwrap() << 52))
    } else {
        None
    }
}

// A positive midpoint between the adjacent `f64`s `below` and `above`, and `want`, the one of
// them whose last bit is 0, to which it rounds to nearest, ties to even.
#[derive(Clone, Copy)]
struct Tie {
    below: f64,
    above: f64,
    want: f64,
}

// The midpoint m 2^e for an odd m in [2^53, 2^54), if it is normal.
fn normal_tie(m: u64, e: i64) -> Tie {
    assert!(m % 2 == 1 && (1 << 53..1 << 54).contains(&m));
    let at = |v: u64| shifted(v as f64, e).unwrap();
    let t = Tie {
        below: at(m - 1),
        above: at(m + 1),
        want: at(m),
    };
    // `as` rounds m to one of the two, and the one with the last bit 0.
    assert!(t.want.to_bits() & 1 == 0 && (t.want == t.below || t.want == t.above));
    t
}

// The midpoint m 2^-1075 for an odd m < 2^54: with m = 2j + 1, the bits of `below` and `above`
// are j and j + 1, of which the even one is that of `want`.
fn subnormal_tie(m: u64) -> Tie {
    assert!(m % 2 == 1 && m < 1 << 54);
    let j = m / 2;
    Tie {
        below: f64::from_bits(j),
        above: f64::from_bits(j + 1),
        want: f64::from_bits(j + j % 2),
    }
}

// `near`, which `what` rounded to nearest gave, has the bits of `want`.
fn expect(what: &str, near: f64, want: f64) {
    assert!(
        near.to_bits() == want.to_bits(),
        "{}: {:e} ({:#x}) to nearest, {:e} ({:#x}) expected",
        what,
        near,
        near.to_bits(),
        want,
        want.to_bits()
    );
}

// Checks x^y, and x^n and (-x)^n for n = y if y is an integer, at the midpoint `t`, and the
// powers at the `f64`s z next to x, which are on one side of the midpoint and not on it: for
// y > 0, z^y is above it if z > x, and then rounds to nearest to `t.above` or beyond it, and is
// below it if z < x, and then rounds to `t.below` or below it; the other way round for y < 0.
fn tie(x: f64, y: f64, t: Tie) {
    let n = if y.fract() == 0.0 {
        Some(y as i32)
    } else {
        None
    };
    check_pow(x, y);
    expect(&format!("pow({:e}, {:e})", x, y), pow_near(x, y), t.want);
    if let Some(n) = n {
        check_pown(x, n);
        check_pown(-x, n);
        expect(&format!("pown({:e}, {})", x, n), pown_near(x, n), t.want);
        // (-x)^n = -(x^n) for an odd n, and rounding to nearest is symmetric.
        let want = if n % 2 == 0 { t.want } else { -t.want };
        expect(&format!("pown({:e}, {})", -x, n), pown_near(-x, n), want);
    }
    for z in [next_down(x), next_up(x)] {
        check_pow(z, y);
        let mut nears = vec![(format!("pow({:e}, {:e})", z, y), pow_near(z, y))];
        if let Some(n) = n {
            check_pown(z, n);
            nears.push((format!("pown({:e}, {})", z, n), pown_near(z, n)));
        }
        let above = (z > x) == (y > 0.0);
        for (what, near) in nears {
            assert!(
                if above {
                    near >= t.above
                } else {
                    near <= t.below
                },
                "{}: {:e} to nearest, but the power is {} the midpoint between {:e} and {:e}",
                what,
                near,
                if above { "above" } else { "below" },
                t.below,
                t.above
            );
        }
    }
}

// The least r with r^n >= 2^b, for b <= 54 and n >= 2.
fn root(b: u32, n: u32) -> u64 {
    let at_least = |r: u64| u128::from(r).checked_pow(n).is_none_or(|p| p >= 1 << b);
    // `at_least` fails at lo and holds at hi, as (2^27)^2 = 2^54.
    let (mut lo, mut hi) = (0, 1 << 27);
    while hi - lo > 1 {
        let mid = (lo + hi) / 2;
        if at_least(mid) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    hi
}

// The odd r >= 3 with r^n in [2^53, 2^54): all of them if there are at most `LIMIT`, and
// otherwise the least, the greatest and `LIMIT` others at random.
fn odd_bases(n: u32, rng: &mut Rng) -> Vec<u64> {
    let first = (root(53, n) | 1).max(3);
    let end = root(54, n);
    if first >= end {
        return vec![];
    }
    let count = (end - first).div_ceil(2);
    if count <= LIMIT {
        (0..count).map(|i| first + 2 * i).collect()
    } else {
        let mut v = vec![first, first + 2 * (count - 1)];
        v.extend((0..LIMIT).map(|_| first + 2 * rng.below(count)));
        v
    }
}

// x^n and x^y for y = n at x = r 2^k, and for an odd n, x^y for y = n/2^j at
// x = r^(2^j) 2^(2^j k) for each j >= 1 with r^(2^j) < 2^53, for the odd r of `odd_bases`, at
// k = 0, at the least and the greatest k for which the midpoint r^n 2^(k n) is normal, which is
// where k n is in [-1075, 970], and at a k between them at random.
#[test]
fn odd_powers() {
    let mut rng = Rng(8101);
    // 3^34 < 2^54 < 3^35.
    for n in 2..=34 {
        for r in odd_bases(n, &mut rng) {
            let m = r.pow(n);
            let n64 = i64::from(n);
            let (lo, hi) = (-(1075 / n64), 970 / n64);
            let k = lo + i64::try_from(rng.below(u64::try_from(hi - lo + 1).unwrap())).unwrap();
            for k in [0, lo, hi, k] {
                let t = normal_tie(m, k * n64);
                // r < 2^27 is an `f64`.
                if let Some(x) = shifted(r as f64, k) {
                    tie(x, f64::from(n), t);
                }
                if n % 2 == 1 {
                    // r^(2^j) < 2^53 is an `f64`, (r^(2^j))^(n/2^j) = r^n, and y = n/2^j is
                    // not an integer. The loop ends before 2^j reaches n, as r^n >= 2^53.
                    let mut j = 1;
                    while let Some(p) = u64::checked_pow(r, 1 << j).filter(|&p| p < 1 << 53) {
                        if let Some(x) = shifted(p as f64, k << j) {
                            tie(x, f64::from(n) / f64::from(1 << j), t);
                        }
                        j += 1;
                    }
                }
            }
        }
    }
}

// The midpoints (2j + 1) 2^-1075 below 2^-1021: x^n = r^n 2^-1075 for an odd r >= 1 with
// r^n < 2^54 and x = r 2^k with k n = -1075, which needs n to divide 1075 = 5^2 43, and
// x^-n = 2^-1075 for x = 2^(1075 / n); and the same with x^2 and y = ±n/2.
#[test]
fn subnormal_midpoints() {
    // 3^5 = 243 = 2 121 + 1, so 3^5 2^-1075 is halfway between 121 2^-1074 and 122 2^-1074.
    expect(
        "pown(3 2^-215, 5)",
        pown_near(3.0 * pow2(-215), 5),
        f64::from_bits(122),
    );
    // 3^25 = 847288609443 = 2 423644304721 + 1, and 423644304721 is odd.
    expect(
        "pown(3 2^-43, 25)",
        pown_near(3.0 * pow2(-43), 25),
        f64::from_bits(423_644_304_722),
    );
    for (n, k) in [(5, -215), (25, -43), (43, -25), (215, -5), (1075, -1)] {
        for r in (1..).step_by(2) {
            let m = match u64::checked_pow(r, n) {
                Some(m) if m < 1 << 54 => m,
                _ => break,
            };
            let t = subnormal_tie(m);
            if m >= 1 << 53 {
                // In the binade of `f64::MIN_POSITIVE`, both ways give the same bits.
                let u = normal_tie(m, -1075);
                assert!(
                    [t.below, t.above, t.want]
                        .iter()
                        .zip([u.below, u.above, u.want])
                        .all(|(a, b)| a.to_bits() == b.to_bits()),
                    "{}^{}",
                    r,
                    n
                );
            }
            // r < 2^11, so r 2^k and r^2 2^(2k) are `f64`s, and normal.
            tie(r as f64 * pow2(k), f64::from(n), t);
            tie((r * r) as f64 * pow2(2 * k), f64::from(n) / 2.0, t);
        }
        let t = subnormal_tie(1);
        tie(pow2(-k), -f64::from(n), t);
        tie(pow2(-2 * k), -f64::from(n) / 2.0, t);
    }
}
