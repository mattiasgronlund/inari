// Tests of the fast path of the powers past the range of `fast_exp` at x < 0, through the signed
// wrappers of `src/cr.rs` at an integer y and through `pown` at odd and even n, and at exact
// subnormal results of `pown`.

use super::*;

// The integers near c: those that c and the 8 `f64`s on each side of it round to, and those
// within 2 of c rounded, so that both parities are there where |c| < 2^53. From 2^52 on, every
// `f64` is an integer, so that n + d is one at any n, and from 2^53 on, every one is even.
fn integers_near(c: f64) -> Vec<f64> {
    let n = c.round();
    let mut ys: Vec<f64> = around(c, 8).into_iter().map(f64::round).collect();
    ys.extend((-2..=2).map(|d| n + f64::from(d)));
    ys.sort_by(f64::total_cmp);
    ys.dedup();
    ys
}

// The |x| of `edge_xs`, and 1 + 2^-43 and 1 + 2^-30, at which t / ln |x| is below 2^53 at every
// t of `th_edges`, so that the integers near it have both parities: from 2^52 to 2^53 at
// 1 + 2^-43, where the next integer moves y ln |x| by about 2^-43, an ulp of th, so that odd y
// reach each t of `th_edges` within an ulp or so (1.5 and 0.7, at which it is below 2^12, are in
// `edge_xs`). At 1 + 2^-52 and 1 - 2^-53 of `edge_xs`, t / ln |x| is above 2^61, where every y is
// even.
fn signed_xs() -> Vec<f64> {
    let mut xs = edge_xs().to_vec();
    xs.extend([1.0 + pow2(-43), 1.0 + pow2(-30)]);
    xs
}

// Whether th is in the arm of `fast_pow_wide_dir` and `fast_pow_wide_near` that calls
// `fast_exp_edge`: out of the range [-707, 709] of `fast_exp`, and between the rules.
fn in_edge_arm(th: f64) -> bool {
    (T_UNDER < th && th < -707.0) || (709.0 < th && th < T_OVER)
}

// x^y rounded toward -∞, toward +∞ and to nearest, ties to even, by the signed wrappers of
// `src/cr.rs`.
fn cr_pow(x: f64, y: f64) -> (f64, f64, f64) {
    (
        crate::cr::pow_rd(x, y),
        crate::cr::pow_ru(x, y),
        crate::cr::pow_rn(x, y),
    )
}

// `lo`, `hi` and `near` are not NaN, and are negative, -0 and -∞ included, exactly if `odd`.
fn check_sign(what: &str, (lo, hi, near): (f64, f64, f64), odd: bool) {
    for v in [lo, hi, near] {
        assert!(
            !v.is_nan() && v.is_sign_negative() == odd,
            "{what}: ({lo:e}, {hi:e}, {near:e}) at an {} exponent",
            if odd { "odd" } else { "even" }
        );
    }
}

// x^y for a finite x < 0 and an integer y through `cr_pow`, as `agree_pow` checks x^y at x > 0:
// the same `f64`s with the fast path as with it disabled, two equal or adjacent ones in the two
// directions with the one to nearest among them, the sign of (-1)^y (`check_sign`), and MPFR's
// roundings on 64-bit Linux and macOS (`mpfr::check_signed`). Returns the rounding tests of the
// fast path that passed and failed in the three calls.
fn agree_signed(x: f64, y: f64) -> (usize, usize) {
    crate::dyadic::fast::reset_fast_counts();
    let fast = cr_pow(x, y);
    let counts = crate::dyadic::fast::fast_counts();
    crate::dyadic::fast::set_fast_path(false);
    let kernel = cr_pow(x, y);
    crate::dyadic::fast::set_fast_path(true);
    let what = format!("pow({:e}, {:e})", x, y);
    assert!(
        fast.0.to_bits() == kernel.0.to_bits()
            && fast.1.to_bits() == kernel.1.to_bits()
            && fast.2.to_bits() == kernel.2.to_bits(),
        "{what}: {fast:?} with the fast path != {kernel:?} without it"
    );
    check_pair(&what, fast.0, fast.1);
    check_near(&what, fast.0, fast.1, fast.2);
    check_sign(&what, fast, is_odd_integer(y));
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    mpfr::check_signed(&what, x, y, fast);
    counts
}

// x^y at x < 0 and an integer y through the signed wrappers of `src/cr.rs`, at the th of
// `th_edges`, as `fast_path_wide_edges` checks x^y at x > 0: y among the integers near
// t / ln |x| for each t and each |x| of `signed_xs`, at which th crosses each t that is an `f64`
// (`T_OVER`, `T_UNDER`, -707 and 709), and at which an odd y reaches the edge arm at each t from
// `T_UNDER` to -707 and from 709 to `T_OVER`. The wrappers call `pow` at |x|, in the other
// direction for an odd y, so that its fast path rounds -x^y there.
#[test]
fn signed_pow_wide_edges() {
    let (mut odd, mut even) = (Tally::default(), Tally::default());
    for s in th_edges() {
        let mut odd_edge = false;
        for x in signed_xs() {
            let ys = integers_near(s / x.ln());
            if [T_OVER, T_UNDER, -707.0, 709.0].contains(&s) {
                let ths: Vec<f64> = ys.iter().map(|&y| pow_t::<HAS_FMA>(x, y).0).collect();
                assert!(
                    ths.iter().any(|&th| th < s) && ths.iter().any(|&th| th > s),
                    "x = {x:e}: th does not cross {s}"
                );
            }
            for y in ys {
                let counts = agree_signed(-x, y);
                if is_odd_integer(y) {
                    odd_edge |= in_edge_arm(pow_t::<HAS_FMA>(x, y).0);
                    odd.add(counts);
                } else {
                    even.add(counts);
                }
            }
        }
        if (T_UNDER..=-707.0).contains(&s) || (709.0..=T_OVER).contains(&s) {
            assert!(odd_edge, "no odd y reaches the edge arm at th = {s}");
        }
    }
    odd.print("signed wide edges, odd y");
    even.print("signed wide edges, even y");
}

// x^n at x < 0 at the th of `th_edges`, as `fast_path_wide_edges` checks it at x > 0, through
// `agree_pown`, whose MPFR comparison covers x < 0, and `check_sign`: n within 2 of t / ln |x|
// for each t and each |x| of `edge_xs` and 1 + 2^-20, where that is an `i32` (|ln |x|| above
// about 2^-21.5), which gives both parities, and at which an odd n reaches the edge arm at each
// t from `T_UNDER` to -707 and from 709 to `T_OVER`. `pown` rounds -(|x|^n) in the other
// direction at an odd n.
#[test]
fn signed_pown_wide_edges() {
    let (mut odd, mut even) = (Tally::default(), Tally::default());
    let mut xs = edge_xs().to_vec();
    xs.push(1.0 + pow2(-20));
    for s in th_edges() {
        let mut odd_edge = false;
        for &x in &xs {
            // `as` saturates, so that an n out of the range of `i32` fails `try_from`.
            let n = (s / x.ln()).round() as i64;
            for m in n - 2..=n + 2 {
                let Ok(m) = i32::try_from(m) else {
                    continue;
                };
                let counts = agree_pown(-x, m);
                let results = (pown(-x, m, false), pown(-x, m, true), pown_near(-x, m));
                check_sign(&format!("pown({:e}, {})", -x, m), results, m % 2 != 0);
                if m % 2 != 0 {
                    odd_edge |= in_edge_arm(pow_t::<HAS_FMA>(x, f64::from(m)).0);
                    odd.add(counts);
                } else {
                    even.add(counts);
                }
            }
        }
        if (T_UNDER..=-707.0).contains(&s) || (709.0..=T_OVER).contains(&s) {
            assert!(odd_edge, "no odd n reaches the edge arm at th = {s}");
        }
    }
    odd.print("signed wide edges of pown, odd n");
    even.print("signed wide edges of pown, even n");
}

// The (r, a, n) of an x = r 2^-a with r in {1, 3, 5, 7} and n >= 2 at which x^n = r^n 2^(-a n)
// is in [2^-1075, 2^-1022) and r^n < 2^53: for an r^n of b bits, x^n is in
// [2^(b - 1 - a n), 2^(b - a n)), so that 1022 + b <= a n <= 1075. x^n is then a subnormal
// `f64` for a n <= 1074, and for a n = 1075 the midpoint between the two subnormals
// (r^n - 1) / 2 2^-1074 and (r^n + 1) / 2 2^-1074, at r = 1 between 0 and 2^-1074.
fn subnormal_powers() -> Vec<(u64, i64, i32)> {
    let mut v = Vec::new();
    for r in [1u64, 3, 5, 7] {
        for n in 2..=1075 {
            let p = match r.checked_pow(n) {
                Some(p) if p < 1 << 53 => p,
                _ => break,
            };
            let (b, n) = (i64::from(64 - p.leading_zeros()), i64::from(n));
            for a in (1022 + b + n - 1) / n..=1075 / n {
                v.push((r, a, i32::try_from(n).unwrap()));
            }
        }
    }
    v
}

// `Some` of the bits of v, to compare the results of the fast path bit for bit.
fn bits(v: Option<f64>) -> Option<u64> {
    v.map(f64::to_bits)
}

// The exact subnormal powers of `subnormal_powers`, such as (2^-537)^2 = 2^-1074,
// (2^-358)^3 = 2^-1074, (3 2^-537)^2 = 9 2^-1074 and the midpoint (2^-215)^5 = 2^-1075, which
// the rules of `pown_pos` leave to the fast path and which reach the edge arm, as th = n ln x is
// in [-1075 ln 2, -1022 ln 2]. Where x^n is an `f64`, no directed test of the fast path can
// pass, as x^n is within the bound of h + l, and the test to nearest gives x^n or fails. At a
// midpoint, the directed tests may pass and give the two subnormals around it, and the test to
// nearest fails: C + y is then half a gap, 2^-53 C, from s, so that |u| is at least
// 2^-53 C - 2 err C, its strict bound. Both directions and nearest give x^n, or the roundings of
// the midpoint, and `agree_pown` checks x^n and (-x)^n.
#[test]
fn exact_subnormal_pown() {
    let cases = subnormal_powers();
    for (r, a, n) in [(1, 537, 2), (1, 358, 3), (3, 537, 2), (1, 215, 5)] {
        assert!(cases.contains(&(r, a, n)), "({r} 2^-{a})^{n} is not a case");
    }
    let (mut t, mut neg) = (Tally::default(), Tally::default());
    for (r, a, n) in cases {
        let x = r as f64 * pow2(-a);
        let y = f64::from(n);
        let what = format!("pown({:e}, {})", x, n);
        let th = pow_t::<HAS_FMA>(x, y).0;
        assert!(in_edge_arm(th), "{what}: th = {th} is not in the edge arm");
        let p = r.pow(n as u32);
        let (lo, hi, near) = if a * i64::from(n) <= 1074 {
            // p < 2^53 and 2^(-a n) are `f64`s, and so is their product, x^n.
            let v = p as f64 * pow2(-a * i64::from(n));
            assert!(
                fast_pow_dir::<HAS_FMA>(x, y, false).is_none()
                    && fast_pow_dir::<HAS_FMA>(x, y, true).is_none(),
                "{what}: a directed test passed at the `f64` {v:e}"
            );
            (v, v, v)
        } else {
            // x^n = p 2^-1075 for an odd p, between q 2^-1074 and (q + 1) 2^-1074.
            let q = (p - 1) / 2;
            let (lo, hi) = (q as f64 * pow2(-1074), (q + 1) as f64 * pow2(-1074));
            let near = if q % 2 == 0 { lo } else { hi };
            for (up, want) in [(false, lo), (true, hi)] {
                let got = fast_pow_dir::<HAS_FMA>(x, y, up);
                assert!(
                    got.is_none() || bits(got) == bits(Some(want)),
                    "{what}: {got:?} toward {} at the midpoint, {want:e} expected",
                    if up { "+∞" } else { "-∞" }
                );
            }
            assert!(
                fast_pow_near::<HAS_FMA>(x, y).is_none(),
                "{what}: the test to nearest passed at the midpoint"
            );
            (lo, hi, near)
        };
        let got = fast_pow_near::<HAS_FMA>(x, y);
        assert!(
            got.is_none() || bits(got) == bits(Some(near)),
            "{what}: {got:?} to nearest, {near:e} expected"
        );
        assert!(
            pown(x, n, false).to_bits() == lo.to_bits()
                && pown(x, n, true).to_bits() == hi.to_bits()
                && pown_near(x, n).to_bits() == near.to_bits(),
            "{what}: not ({lo:e}, {hi:e}) and {near:e} to nearest"
        );
        t.add(agree_pown(x, n));
        let results = (pown(-x, n, false), pown(-x, n, true), pown_near(-x, n));
        check_sign(&format!("pown({:e}, {})", -x, n), results, n % 2 != 0);
        neg.add(agree_pown(-x, n));
    }
    t.print("exact subnormal powers");
    neg.print("exact subnormal powers of -x");
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod mpfr {
    use crate::mpfr_calls::mpfr::{pow_rd, pow_rn, pow_ru};

    fn same(a: f64, b: f64) -> bool {
        a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
    }

    // `lo`, `hi` and `near`, which the signed wrappers of `src/cr.rs` gave at (x, y), are MPFR's
    // roundings toward -∞, toward +∞ and to nearest, ties to even, which `pow_rn` rounds once
    // with the subnormals of an `f64`. At x < 0 and an integer y, MPFR gives (-1)^y |x|^y, as
    // the wrappers do; `check_pow` of `tests.rs` skips x < 0, where `pow` gives NaN.
    pub(super) fn check_signed(what: &str, x: f64, y: f64, (lo, hi, near): (f64, f64, f64)) {
        let want = (pow_rd(x, y), pow_ru(x, y), pow_rn(x, y));
        assert!(
            same(lo, want.0) && same(hi, want.1) && same(near, want.2),
            "{what}: ({lo:e}, {hi:e}, {near:e}) != MPFR's {want:?}"
        );
    }
}
