// Tests of the fast path of the powers of the dyadic kernel past the range of `fast_exp`, on
// random arguments over the binades of subnormal results and the last finite binade, and the
// fall-through of its edge arm, through `agree_pow` and `agree_pown` of `tests.rs`.

use super::*;
use crate::dyadic::fast::fast_two_sum;
use std::f64::consts::LN_2;

// The ranges of x of `binade_arg`: within 2^-40 to 2^-20 of 1, in [1/2, 2], and log-uniform
// over the positive `f64`s.
const RANGES: [&str; 3] = ["near 1", "[1/2, 2]", "log-uniform"];

// x != 1 at random in the range `r` of `RANGES`, and y = t / ln x for t uniform in
// [k ln 2, (k + 1) ln 2), so that x^y = e^t is in [2^k, 2^(k + 1)) up to the roundings of
// ln x and of the quotient.
fn binade_arg(rng: &mut Rng, k: i64, r: usize) -> (f64, f64) {
    let x = loop {
        let x = match r {
            0 => {
                let d = log_uniform(rng, -40, -21);
                1.0 + sign(rng) * d
            }
            1 => 0.5 + 1.5 * unit(rng),
            _ => log_uniform(rng, -1074, 1023),
        };
        if x != 1.0 {
            break x;
        }
    };
    let t = (k as f64 + unit(rng)) * LN_2;
    (x, t / x.ln())
}

// Whether x^y takes the edge arm of the fast path: th is out of the range of `fast_exp` but
// strictly between the bounds of the rules, so that `fast_pow_wide_dir` and
// `fast_pow_wide_near` round e^(th + tl) from `fast_exp_edge`.
fn edge_arm(x: f64, y: f64) -> bool {
    let th = pow_t(x, y).0;
    fast_pow(x, y).is_none() && T_UNDER < th && th < T_OVER
}

// x^y on random arguments over each binade [2^k, 2^(k + 1)) of results from k = -1077 to -1023,
// the subnormal results and those below 2^-1074, and at k = 1023, the last finite binade, for x
// from each range of `RANGES`, as `agree_pow` checks them, and x^n where n, the integer nearest
// to y, is an `i32` with |n| >= 2, as `agree_pown` checks it. All of the x^y take the edge arm
// but those of the binade 2^-1077 whose th is at most `T_UNDER` (t from -1077 ln 2 = -746.52 to
// -746, about 3/4 of that binade), where the rule settles them. x^n takes it where n ln x is
// still in one of these binades: near 1 and in [1/2, 2], |ln x| < ln 2, so that n ln x is within
// ln 2 / 2 of t, but a log-uniform x has |ln x| up to 744, and n ln x is often far from t, past
// the rules or in the range of `fast_exp`. Most rounding tests pass, as in `edges_random` of
// `src/dyadic/exp/tests.rs`: with this seed, the test fails at 1, 0 and 3 of the 16800 calls of
// x^y in the three ranges, the three roundings of 5600 arguments, and at 0, 1 and 0 of those of
// x^n. With C = 2^(-1022 - e) and u as in `narrow`,
// three of the five are tests to nearest with |u| within 2^-66 C of 2^-53 C, half the gap at s:
// two of x^y at midpoints C + h of two `f64`s, at e = -1027 and -1040, where |l| < 2^-66 C, and
// one of x^n at e = -1051, where C + h is not a midpoint. The other two are the directed tests
// of one x^y at e = -1059, where |u| < 2^-66 C. At k = 1023, the band from (1024 - 1/8192) ln 2
// to 1024 ln 2, where `fast_exp_edge` gives e = 1024 and the tests return `None` without a
// test, is 1/8192 of the binade.
#[test]
fn edges_random() {
    let mut rng = Rng(981);
    let binades: Vec<i64> = (-1077..=-1023).chain([1023]).collect();
    for (r, range) in RANGES.iter().enumerate() {
        let (mut tp, mut tn) = (Tally::default(), Tally::default());
        let (mut pow_calls, mut pow_edge, mut pown_calls, mut pown_edge) = (0, 0, 0, 0);
        for &k in &binades {
            let mut edge = 0;
            for _ in 0..100 {
                let (x, y) = binade_arg(&mut rng, k, r);
                edge += usize::from(edge_arm(x, y));
                tp.add(agree_pow(x, y));
                // `as` saturates, so that an n out of the range of `i32` fails `try_from`.
                if let Ok(n) = i32::try_from(y.round() as i64) {
                    if n.unsigned_abs() >= 2 {
                        pown_calls += 1;
                        pown_edge += usize::from(edge_arm(x, f64::from(n)));
                        tn.add(agree_pown(x, n));
                    }
                }
            }
            // At k = -1077, th <= `T_UNDER` for about 3/4 of the t.
            let least = if k == -1077 { 10 } else { 95 };
            assert!(
                edge >= least,
                "x {range}, results in [2^{k}, 2^{}): {edge} of 100 x^y take the edge arm",
                k + 1
            );
            pow_calls += 100;
            pow_edge += edge;
        }
        tp.print(&format!("pow, x {range}"));
        tn.print(&format!("pown, x {range}"));
        eprintln!(
            "edge arm, x {range}: {pow_edge} of {pow_calls} x^y, {pown_edge} of {pown_calls} x^n"
        );
        assert!(
            2 * pow_edge > pow_calls,
            "x {range}: {pow_edge} of {pow_calls} x^y take the edge arm"
        );
        if r < 2 {
            assert!(
                2 * pown_edge > pown_calls,
                "x {range}: {pown_edge} of {pown_calls} x^n take the edge arm"
            );
        }
        for (name, t) in [("pow", &tp), ("pown", &tn)] {
            assert!(
                t.calls == 0 || t.passed > 100 * t.failed,
                "{name}, x {range}: {} passed, {} failed",
                t.passed,
                t.failed
            );
        }
    }
}

// Whether a directed test of `round_dir_wide_err` and the test of `round_near_wide_err` pass
// narrowly at (h, l, e) with the bound `ERR67`: they pass, but fail with `WIDE` in place of it.
// Where they round C + y on the grid of the `f64`s in [C, 2C] (`round_dir_sub_err` and
// `round_near_sub_err`), with s + t = C + h, they compare |u| for u = RN(t + l) with
// 2 ERR67 C = 2^-66 C in the directions, and with 2^-53 C, half the gap at s, less 2^-66 C to
// nearest, and plus 2^-66 C in the far arms, which only a C + h at a midpoint of two `f64`s
// reaches, and 2 WIDE C = 2^-56 C in place of 2^-66 C makes them fail. Elsewhere, below e = 1024,
// `round_dir_err` and `round_near_err` compare l with `ERR67`, and with half the gaps at h less
// `ERR67`, as in `widened` of `tests.rs`.
fn narrow(h: f64, l: f64, e: i64) -> (bool, bool) {
    if e > 1023 {
        (false, false)
    } else if e < -1022 || (e == -1022 && h <= 1.0) {
        let c = pow2(-1022 - e);
        let (s, t) = fast_two_sum(c, h);
        let u = (t + l).abs();
        // 2^-66 C, 2^-56 C and 2^-53 C, exact as C is a power of 2.
        let (err, wide, half) = (2.0 * ERR67 * c, 2.0 * WIDE * c, f64::EPSILON / 2.0 * c);
        (
            s < 2.0 * c && err < u && u <= wide,
            s < 2.0 * c
                && ((u < half - err && u >= half - wide) || (u > half + err && u <= half + wide)),
        )
    } else {
        // Half the gap between h and the next `f64` above it, and below it.
        let above = if h >= 1.0 {
            f64::EPSILON / 2.0
        } else {
            f64::EPSILON / 4.0
        };
        let below = if h > 1.0 {
            f64::EPSILON / 2.0
        } else {
            f64::EPSILON / 4.0
        };
        (
            ERR67 < l.abs() && l.abs() <= WIDE,
            l < above - ERR67
                && l > -(below - ERR67)
                && (l >= above - WIDE || l <= -(below - WIDE)),
        )
    }
}

// `widened` of `tests.rs` on the edge arm of the fast path, on the arguments of `edges_random`:
// at the (h, l, e) of `fast_exp_edge` where a rounding test passes narrowly (`narrow`), the
// same test with `WIDE` returns `None`, and x^y is the same with the fast path as without it,
// and as MPFR's (`agree_pow`), as an error in the bound would show there first. There are at
// least 20 narrow passes of each kind on the results below 2^-1022, where `round_dir_sub_err`
// and `round_near_sub_err` decide, and on those from 2^1023 to 2^1024, where `round_dir_err`
// and `round_near_err` do at e = 1023. With this seed, 214 and 259 of the 2000 arguments below
// 2^-1022 pass a directed test and the test to nearest narrowly (8 of the 259 on the far side
// of a midpoint C + h, |u| > 2^-53 C), and 63 and 53 of the 1000 at the top. None does from
// 2^-1077 to 2^-1076, where C >= 2^54, s = C and u = h + l is above 2^-56 C and below
// 2^-53 C - 2^-56 C.
#[test]
fn edges_widened() {
    let mut rng = Rng(982);
    let sub: Vec<i64> = (-1077..=-1023).collect();
    for (what, binades, count) in [("below 2^-1022", sub, 2000), ("top", vec![1023], 1000)] {
        let (mut dir, mut near) = (0, 0);
        for i in 0..count {
            let k = binades[i % binades.len()];
            let (x, y) = binade_arg(&mut rng, k, i % RANGES.len());
            if !edge_arm(x, y) {
                continue;
            }
            let (th, tl) = pow_t(x, y);
            let (h, l, e) = fast_exp_edge(th, tl).unwrap();
            let (narrow_dir, narrow_near) = narrow(h, l, e);
            for up in [false, true].into_iter().filter(|_| narrow_dir) {
                assert!(
                    round_dir_wide_err(h, l, e, ERR67, up).is_some()
                        && round_dir_wide_err(h, l, e, WIDE, up).is_none(),
                    "pow({x:e}, {y:e}), up = {up}: ({h:e}, {l:e}, {e}) passes the directed \
                     test with WIDE, or fails it with ERR67"
                );
            }
            if narrow_near {
                assert!(
                    round_near_wide_err(h, l, e, ERR67).is_some()
                        && round_near_wide_err(h, l, e, WIDE).is_none(),
                    "pow({x:e}, {y:e}): ({h:e}, {l:e}, {e}) passes the test to nearest with \
                     WIDE, or fails it with ERR67"
                );
            }
            if !narrow_dir && !narrow_near {
                continue;
            }
            dir += usize::from(narrow_dir);
            near += usize::from(narrow_near);
            agree_pow(x, y);
        }
        eprintln!("narrow passes, {what}: {dir} directed, {near} to nearest");
        assert!(
            dir >= 20 && near >= 20,
            "{what}: {dir} narrow passes of the directed tests and {near} of the test to nearest"
        );
    }
}

// u / C at (h, l, e) where `round_near_wide_err` rounds with `round_near_sub_err` and C + h is
// a midpoint of two `f64`s of [C, 2C) below 2C: |t| = 2^-53 C for (s, t) = Fast2Sum(C, h),
// with s < 2C, and u = RN(t + l). `None` elsewhere. The quotient is exact, as C is a power of 2.
fn sub_tie(h: f64, l: f64, e: i64) -> Option<f64> {
    if e > -1022 || (e == -1022 && h > 1.0) {
        return None;
    }
    let c = pow2(-1022 - e);
    let (s, t) = fast_two_sum(c, h);
    (s < 2.0 * c && t.abs() == f64::EPSILON / 2.0 * c).then(|| (t + l) / c)
}

// The far arms of `round_near_sub_err` on random arguments of `edges_random` from 2^-1030 to
// 2^-1022: where C + h is a midpoint (`sub_tie`) and |u| > (2^-53 + 2^-66) C, the test to
// nearest of x^y passes, and x^y is the same with the fast path as without it, and as MPFR's
// (`agree_pow`). All 800 x^y of each range take the edge arm. With this seed, 100, 109 and 92
// of them are at midpoints (x near 1, in [1/2, 2] and log-uniform), and 35, 59 and 55 of those
// take a far arm. None has |u| within 2^-66 C of 2^-53 C, so that the others take the arm of s.
// The test asks for about half of the far ones.
#[test]
fn far_side_ties() {
    use crate::dyadic::fast::{fast_counts, reset_fast_counts};
    let mut rng = Rng(984);
    // 2^-53 + 2^-66 and 2^-53 - 2^-66, exact.
    let (far, near) = (
        f64::EPSILON / 2.0 + 2.0 * ERR67,
        f64::EPSILON / 2.0 - 2.0 * ERR67,
    );
    for (r, range) in RANGES.iter().enumerate() {
        let (mut calls, mut ties, mut found, mut within) = (0, 0, 0, 0);
        for k in -1030..=-1023 {
            for _ in 0..100 {
                let (x, y) = binade_arg(&mut rng, k, r);
                if !edge_arm(x, y) {
                    continue;
                }
                calls += 1;
                let (th, tl) = pow_t(x, y);
                let (h, l, e) = fast_exp_edge(th, tl).unwrap();
                let Some(u) = sub_tie(h, l, e) else {
                    continue;
                };
                ties += 1;
                if u.abs() > far {
                    found += 1;
                    reset_fast_counts();
                    pow_near(x, y);
                    assert_eq!(fast_counts(), (1, 0), "pow({x:e}, {y:e}) to nearest");
                    agree_pow(x, y);
                } else if u.abs() >= near {
                    within += 1;
                    eprintln!(
                        "pow({x:e}, {y:e}): ({h:e}, {l:e}, {e}), u = {u:e} C, within 2^-66 C of \
                         a midpoint"
                    );
                }
            }
        }
        eprintln!(
            "midpoints, x {range}: {ties} of {calls} x^y, {found} far, {within} within 2^-66 C"
        );
        let least = [17, 29, 27][r];
        assert!(
            found >= least,
            "x {range}: {found} of {ties} midpoints take a far arm"
        );
    }
}

// `round_near_wide_err` at constructed midpoints, where `round_near_sub_err` decides: for
// C = 2^(-1022 - e), g = 2^-52 C and h = (m + 1/2) g, C + h is the midpoint of C + m g and
// C + (m + 1) g, which Fast2Sum rounds to the even one, s, with t = g/2 for an even m and -g/2
// for an odd one. (h + l) 2^e = (m + 1/2 + l / g) 2^-1074 rounds to the `f64` whose bits are
// m + 1 where l > 0 and m where l < 0, as 0 < |l / g| < 1/2. The m are at least 2^50, so
// that ulp(h) / 2 >= 2^-55 C is above the |l| <= 2^-56 C used here, and u = t + l is exact. Not
// every h is in (1/2, 2), the range of the fast paths, which this arithmetic does not need:
// (2^50 + 3/2) g is below 1/2 at e = -1022, and at e = -1030 every h is above 2^6, as an |l| of
// 2^-56 C = 2^-48 needs ulp(h) / 2 >= 2^-48, which no h < 2 has. With
// `ERR67`, a far arm gives that `f64` where |u| is in ((2^-53 + 2^-66) C, (2^-53 + 2^-56) C],
// and the arm of s gives it where |u| is in [(2^-53 - 2^-56) C, (2^-53 - 2^-66) C). The
// comparisons are strict, so that |u| = (2^-53 +- 2^-66) C fails, and with `WIDE`, all of these
// fail, as 2 WIDE C = 2^-56 C. At m = 2^52 - 1, C + h = 2C - g/2 rounds to s = 2C, where the
// gap above s is 2g, and the test fails whatever l.
#[test]
fn constructed_ties() {
    // 2^-53, 2^-66 and 2^-56, in units of C.
    let (half, err, wide) = (f64::EPSILON / 2.0, 2.0 * ERR67, 2.0 * WIDE);
    // The distances of |u| / C from 2^-53 that the tests take, on both sides: at the bound of
    // `ERR67`, just past it, between the bounds and at the bound of `WIDE`.
    let ds = [err, err + pow2(-74), pow2(-60), wide];
    for e in [-1022, -1023, -1030] {
        let c = pow2(-1022 - e);
        let g = f64::EPSILON * c;
        for m in [
            (1_u64 << 50) + 1,
            (1 << 51) + 2,
            (1 << 52) - 3,
            (1 << 52) - 2,
        ] {
            // (m + 1/2) g = (2m + 1) g/2, exact as 2m + 1 < 2^53.
            let h = (2 * m + 1) as f64 * (g / 2.0);
            let (s, t) = fast_two_sum(c, h);
            let sign = if m % 2 == 0 { 1.0 } else { -1.0 };
            assert!(
                s < 2.0 * c && t == sign * g / 2.0 && (e < -1022 || h <= 1.0),
                "({h:e}, {e}): s = {s:e}, t = {t:e}"
            );
            let half_ulp = (f64::from_bits(h.to_bits() + 1) - h) / 2.0;
            for (d, far) in ds.iter().flat_map(|&d| [(d, true), (d, false)]) {
                let l = if far { sign * d * c } else { -sign * d * c };
                let side = if far { half + d } else { half - d };
                assert!(
                    l.abs() <= half_ulp && (t + l).abs() == side * c,
                    "({h:e}, {l:e}, {e}): not a valid pair, or u is not exact"
                );
                let bits = (d != err).then_some(if l > 0.0 { m + 1 } else { m });
                assert_eq!(
                    round_near_wide_err(h, l, e, ERR67).map(f64::to_bits),
                    bits,
                    "({h:e}, {l:e}, {e}) with ERR67"
                );
                assert_eq!(
                    round_near_wide_err(h, l, e, WIDE),
                    None,
                    "({h:e}, {l:e}, {e}) with WIDE"
                );
            }
        }
    }
    let (e, c) = (-1023, 2.0);
    // h = (2^52 - 1/2) g = C - g/2 = 2 - 2^-52, for g = 2^-51.
    let h = ((1_u64 << 53) - 1) as f64 * pow2(-52);
    assert_eq!(fast_two_sum(c, h).0, 2.0 * c);
    for l in ds.iter().flat_map(|&d| [d * c, -d * c]) {
        assert_eq!(
            round_near_wide_err(h, l, e, ERR67),
            None,
            "({h:e}, {l:e}, {e})"
        );
    }
}

// The rounding tests that `fast_pow_dir` and `fast_pow_near` take on the edge arm, as
// `fast_counts` counts them, and the arguments at which they take none:
// - on random arguments of `edges_random`, which all take the edge arm, all 900 pass with this
//   seed, those to nearest at midpoints C + h included (`far_side_ties`);
// - at the exact 2^1023 (x = 2, y = 1023), 2^-1074 = (2^-537)^2 and 2^-1060 = (1/2)^1060, which
//   take it, both directed tests fail, as h + l is within the bound of an `f64` (scaled to 1, or
//   to the grid of C + y), and the test to nearest passes and gives that `f64`;
// - where `fast_exp_edge` gives e = 1024, from th = (1024 - 1/8192) ln 2 to below `T_OVER`
//   (2^(1024 - 2^-20) and random x^y in that band), `round_dir_wide_err` and
//   `round_near_wide_err` return `None` before any test, so that nothing is counted and the
//   kernel computes x^y;
// - the rules count nothing either: at th >= `T_OVER`, `fast_pow_dir` gives `overflow(up)` and
//   `fast_pow_near` +∞, and at th <= `T_UNDER`, `underflow(up)` and +0. The y next to
//   `T_OVER / ln x` and `T_UNDER / ln x` put th on both sides of each: below `T_OVER`, in the band
//   of e = 1024, nothing is counted either, and above `T_UNDER` the three tests are counted.
#[test]
fn edge_counts() {
    use crate::dyadic::fast::{fast_counts, reset_fast_counts};
    let mut rng = Rng(983);
    let (mut passed, mut failed) = (0, 0);
    reset_fast_counts();
    for i in 0..300 {
        let k = [-1076, -1050, -1023, 1023][i % 4];
        let (x, y) = binade_arg(&mut rng, k, i % RANGES.len());
        assert!(
            edge_arm(x, y),
            "pow({x:e}, {y:e}) does not take the edge arm"
        );
        fast_pow_dir(x, y, false);
        fast_pow_dir(x, y, true);
        fast_pow_near(x, y);
    }
    let (p, f) = fast_counts();
    assert!(p + f == 900 && p > 20 * f, "random: {p} passed, {f} failed");
    eprintln!("edge arm, random: {p} tests passed, {f} failed");
    (passed, failed) = (passed + p, failed + f);
    for (x, y, v) in [
        (2.0, 1023.0, pow2(1023)),
        (pow2(-537), 2.0, pow2(-1074)),
        (0.5, 1060.0, pow2(-1060)),
    ] {
        assert!(
            edge_arm(x, y),
            "pow({x:e}, {y:e}) does not take the edge arm"
        );
        reset_fast_counts();
        for up in [false, true] {
            assert!(
                fast_pow_dir(x, y, up).is_none(),
                "pow({x:e}, {y:e}), up = {up}"
            );
        }
        assert_eq!(fast_pow_near(x, y), Some(v), "pow({x:e}, {y:e}) to nearest");
        assert_eq!(fast_counts(), (1, 2), "pow({x:e}, {y:e})");
        (passed, failed) = (passed + 1, failed + 2);
    }
    let mut band = vec![(2.0, 1024.0 - pow2(-20))];
    for i in 0..60 {
        let x = binade_arg(&mut rng, 1023, i % RANGES.len()).0;
        // t from (1024 - 0.9 / 8192) ln 2 to (1024 - 0.1 / 8192) ln 2, inside the band.
        let t = (1024.0 - (0.1 + 0.8 * unit(&mut rng)) / 8192.0) * LN_2;
        band.push((x, t / x.ln()));
    }
    for (x, y) in band {
        let (th, tl) = pow_t(x, y);
        assert!(
            edge_arm(x, y) && fast_exp_edge(th, tl).unwrap().2 == 1024,
            "pow({x:e}, {y:e}): th = {th} is not in the band of e = 1024"
        );
        reset_fast_counts();
        for up in [false, true] {
            assert!(
                fast_pow_dir(x, y, up).is_none(),
                "pow({x:e}, {y:e}), up = {up}"
            );
        }
        assert!(
            fast_pow_near(x, y).is_none(),
            "pow({x:e}, {y:e}) to nearest"
        );
        assert_eq!(fast_counts(), (0, 0), "pow({x:e}, {y:e})");
        agree_pow(x, y);
    }
    let xs = [
        2.0,
        0.5,
        1.0 + pow2(-30),
        1.0 - pow2(-30),
        1.5,
        1.1 * pow2(-1000),
        1.7 * pow2(1000),
    ];
    for x in xs {
        let (mut rule_over, mut rule_under, mut left_over, mut left_under) = (0, 0, 0, 0);
        let mut ys = around(T_OVER / x.ln(), 4);
        ys.extend(around(T_UNDER / x.ln(), 4));
        ys.extend([800.0, -800.0, 1e4, -1e4].map(|t| t / x.ln()));
        for y in ys {
            let th = pow_t(x, y).0;
            reset_fast_counts();
            let (lo, hi, near) = (
                fast_pow_dir(x, y, false),
                fast_pow_dir(x, y, true),
                fast_pow_near(x, y),
            );
            let counts = fast_counts();
            if th >= T_OVER {
                rule_over += 1;
                assert!(
                    lo == Some(overflow(false))
                        && hi == Some(overflow(true))
                        && near == Some(f64::INFINITY)
                        && counts == (0, 0),
                    "pow({x:e}, {y:e}), th = {th}: {lo:?} {hi:?} {near:?}, counts {counts:?}"
                );
            } else if th <= T_UNDER {
                rule_under += 1;
                assert!(
                    lo == Some(underflow(false))
                        && hi == Some(underflow(true))
                        && near.map(f64::to_bits) == Some(0)
                        && counts == (0, 0),
                    "pow({x:e}, {y:e}), th = {th}: {lo:?} {hi:?} {near:?}, counts {counts:?}"
                );
            } else if th > 0.0 {
                left_over += 1;
                assert!(
                    lo.is_none() && hi.is_none() && near.is_none() && counts == (0, 0),
                    "pow({x:e}, {y:e}), th = {th}: {lo:?} {hi:?} {near:?}, counts {counts:?}"
                );
            } else {
                left_under += 1;
                assert!(
                    counts.0 + counts.1 == 3,
                    "pow({x:e}, {y:e}), th = {th}: counts {counts:?}"
                );
                (passed, failed) = (passed + counts.0, failed + counts.1);
            }
        }
        assert!(
            rule_over > 0 && rule_under > 0 && left_over > 0 && left_under > 0,
            "x = {x:e}: th on each side of the rules {rule_over}, {left_over}, {left_under}, \
             {rule_under} times"
        );
    }
    eprintln!("edge arm, all: {passed} tests passed, {failed} failed");
    assert!(passed > 0 && failed > 0);
}
