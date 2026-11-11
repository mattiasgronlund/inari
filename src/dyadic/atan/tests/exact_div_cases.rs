// Tests of `exact_div`, `tiny_quotient` and `midpoint_quotient` at chosen arguments: the false
// positives of the bare residual, at which q = y / x rounded to nearest gives q x - y = 0 after
// rounding while y / x is not an `f64`, the thresholds of the two rules and of `exact_div`'s
// scale and guard, and the midpoints between two `f64`s below 2^-1021.
//
// Each case is checked, for y and for -y, by bits against the `Dyadic` references, `exact_ref`
// below for `exact_div` and `tiny_quotient_old` and `midpoint_quotient_old` for the two rules
// (`same_map`), and with `check2_fast`, which compares atan2 with and without the fast path, and
// with MPFR on 64-bit Linux and macOS (`check_refs`), and, where the test states the values,
// against them (`check_case`).

use super::*;

// y / x if it is an `f64`, and `None` otherwise, for finite y != 0 and x > 0, with the
// `Dyadic` division at 1 limb: `tiny_quotient_dyadic` without its bound `TINY_HYP`.
fn exact_ref(y: f64, x: f64) -> Option<f64> {
    let (a, b) = (Dyadic::<1>::from_f64(y), Dyadic::<1>::from_f64(x));
    let (lo, hi) = (a.div(&b, false), a.div(&b, true));
    let q = lo.to_f64(false);
    if q == hi.to_f64(true) {
        Some(q)
    } else {
        None
    }
}

fn bits(v: Option<f64>) -> Option<u64> {
    v.map(f64::to_bits)
}

// q = y / x rounded to nearest if q x - y rounds to 0 with an FMA, which is what the bare
// residual would take for an exact quotient.
fn bare(y: f64, x: f64) -> Option<f64> {
    let q = y / x;
    if q.mul_add(x, -y) == 0.0 {
        Some(q)
    } else {
        None
    }
}

// Checks (y, x) and (-y, x), for finite y != 0 and x > 0, against the references, by bits:
// `exact_div` against `exact_ref` where its contract holds, |y| < x < 2^996, and the two rules
// through `same_map`; and with `check2_fast`.
fn check_refs(y: f64, x: f64) {
    for y in [y, -y] {
        if y.abs() < x && x < TWO_996 {
            assert_eq!(
                bits(exact_div(y, x)),
                bits(exact_ref(y, x)),
                "exact_div({:e}, {:e})",
                y,
                x
            );
        }
        same_map(y, x);
        check2_fast(y, x);
    }
}

// `check_refs` at (y, x), and the values that the test states for y > 0: `quotient`, y / x if
// it is an `f64`, and `midpoint`, the `f64` next to y / x toward zero if y / x is midway between
// two `f64`s below 2^-1021 (as `midpoint_quotients` of `tests.rs` says), each `None` otherwise,
// and their negations for -y. Then `exact_ref`, and `exact_div` where its contract holds, give
// `quotient`, `tiny_quotient` gives it below `TINY_HYP`, and `midpoint_quotient` gives
// `midpoint`, by bits, so that the sign of a zero counts. atan2 rounds to nearest to
// `midpoint`, and to `quotient` below `TINY_NEAR`. Its directed roundings are, toward zero and
// away from it, `midpoint` and the `f64` after it, and below `TINY_HYP` the `f64` before
// `quotient` and `quotient` itself: atan t is in (t - t^3 / 3, t) for t in (0, 1], and
// t^3 / 3 < t 2^-53 there, less than the step below t.
fn check_case(y: f64, x: f64, quotient: Option<f64>, midpoint: Option<f64>) {
    check_refs(y, x);
    for s in [1.0, -1.0] {
        let (y, quotient, midpoint) = (s * y, quotient.map(|q| s * q), midpoint.map(|f| s * f));
        let args = format!("{:e}, {:e}", y, x);
        assert_eq!(bits(exact_ref(y, x)), bits(quotient), "exact_ref({})", args);
        if y.abs() < x && x < TWO_996 {
            assert_eq!(bits(exact_div(y, x)), bits(quotient), "exact_div({})", args);
        }
        let tiny = quotient.filter(|q| q.abs() < TINY_HYP);
        assert_eq!(
            bits(tiny_quotient(y, x)),
            bits(tiny),
            "tiny_quotient({})",
            args
        );
        assert_eq!(
            bits(midpoint_quotient(y, x)),
            bits(midpoint),
            "midpoint_quotient({})",
            args
        );
        let near = match midpoint {
            Some(f) => Some(f),
            None => quotient.filter(|q| q.abs() < TINY_NEAR),
        };
        if let Some(r) = near {
            assert_eq!(
                atan2_near(y, x).to_bits(),
                r.to_bits(),
                "atan2({}) to nearest",
                args
            );
        }
        // The `f64` after or before v, away from zero for y > 0 and toward it for y < 0.
        let step = |v: f64| if y > 0.0 { next_up(v) } else { next_down(v) };
        let ends = match (midpoint, tiny) {
            (Some(f), _) => Some((f, step(f))),
            (None, Some(q)) => Some((-step(-q), q)),
            _ => None,
        };
        if let Some((toward, away)) = ends {
            let (down, up) = if y > 0.0 {
                (toward, away)
            } else {
                (away, toward)
            };
            assert_eq!(
                atan2(y, x, false).to_bits(),
                down.to_bits(),
                "atan2({}) down",
                args
            );
            assert_eq!(
                atan2(y, x, true).to_bits(),
                up.to_bits(),
                "atan2({}) up",
                args
            );
        }
    }
}

// The bits that `rocq/theories/Model.v` gives `two_m968`, `two_128`, `two_996` and
// `two_m1021`, and the powers of 2 that their names say.
#[test]
fn exact_div_constants() {
    assert_eq!(TWO_M968.to_bits(), 0x0370_0000_0000_0000);
    assert_eq!(TWO_128.to_bits(), 0x47f0_0000_0000_0000);
    assert_eq!(TWO_996.to_bits(), 0x7e30_0000_0000_0000);
    assert_eq!(TWO_M1021.to_bits(), 0x0020_0000_0000_0000);
    assert_eq!(TWO_M968, pow2(-968));
    assert_eq!(TWO_128, pow2(128));
    assert_eq!(TWO_996, pow2(996));
    assert_eq!(TWO_M1021, pow2(-1021));
}

// The false positives of the bare residual, at which `exact_div` and the two rules give `None`:
// - y = ±2^-1073 with x = 1 + 2^-52 and x = 1 - 2^-53: q = y, and q x - y = ±2^-1125 or
//   ∓2^-1126 rounds to 0. At x = 1 - 2^-53, y / x is just above 2^-1073, and atan2 rounds down
//   to 2^-1073 and up to 3 2^-1074, where the bare residual would give `toward_zero(q)`, 2^-1074
//   and 2^-1073. With the scale 2^128 the product q 2^128 x is not y 2^128.
// - y = ±2^-1074 with x = 2/3 rounded, which is (2/3)(1 - 2^-54): 2y / x rounds to 3 2^-1074,
//   whose bits are odd, and 3x - 2 = -2^-53 gives 3 2^-1074 x - 2y = -2^-1127, which rounds to
//   0. y / x is just above 1.5 2^-1074, so that atan2 rounds to nearest to ±2^-1073, where the
//   bare residual would give the midpoint rule's ±2^-1074. With the scale, 3 2^-946 x =
//   2^-945 - 2^-999 rounds to nearest even 2^-945, which is 2y 2^128: here the product passes,
//   and only its error, -2^-999, rejects the quotient.
// - subnormal y = Y 2^-1074 and x = X 2^-1074, X in {3, 5, 2^26 + 1, 3 2^30 + 1, 2^52 - 1, 4,
//   12} and Y < X in {1, 3, 7, X - 2, 2^51 + 1}: y / x = Y / X is an `f64` only at Y / X = 1/4,
//   3/12, 2/4 and 3/4, and every other one is a false positive, as q = Y / X
//   rounded to nearest gives |q X - Y| <= Y 2^-53 < 1/2, so that q x - y rounds to 0. The
//   pretest of `midpoint_quotient` leaves out all of them.
#[test]
fn exact_div_false_positives() {
    let (a, b) = (1.0 + f64::EPSILON, 1.0 - f64::EPSILON / 2.0);
    for x in [a, b] {
        let y = pow2(-1073);
        for y in [y, -y] {
            assert_eq!(
                bits(bare(y, x)),
                Some(y.to_bits()),
                "bare({:e}, {:e})",
                y,
                x
            );
        }
        check_case(y, x, None, None);
    }
    // At x = 1 + 2^-52, atan2 gives what the bare residual would, as y / x is below 2^-1073.
    let y = pow2(-1073);
    let (t, t3) = (pow2(-1074), f64::from_bits(3));
    for (x, down, up) in [(a, t, y), (b, y, t3)] {
        assert_eq!(atan2(y, x, false), down, "atan2({:e}, {:e}) down", y, x);
        assert_eq!(atan2(y, x, true), up, "atan2({:e}, {:e}) up", y, x);
        assert_eq!(atan2(-y, x, false), -up, "atan2({:e}, {:e}) down", -y, x);
        assert_eq!(atan2(-y, x, true), -down, "atan2({:e}, {:e}) up", -y, x);
        assert_eq!(atan2_near(y, x), y, "atan2({:e}, {:e}) to nearest", y, x);
        assert_eq!(atan2_near(-y, x), -y, "atan2({:e}, {:e}) to nearest", -y, x);
    }
    // The rule of `atan2` on the bare residual's quotient would give these.
    let q = bare(y, b).unwrap();
    assert_ne!(toward_zero(q, false), atan2(y, b, false));
    assert_ne!(toward_zero(q, true), atan2(y, b, true));

    let (y, x) = (pow2(-1074), 2.0 / 3.0);
    assert_eq!(3.0_f64.mul_add(x, -2.0), -f64::EPSILON / 2.0);
    for y in [y, -y] {
        let args = format!("{:e}, {:e}", y, x);
        let q2 = bare(2.0 * y, x);
        assert_eq!(
            bits(q2),
            Some((3.0 * y).to_bits()),
            "bare(2y, x) at {}",
            args
        );
        assert_eq!(
            bits(exact_div(2.0 * y, x)),
            None,
            "exact_div(2y, x) at {}",
            args
        );
        assert_eq!(
            bits(exact_ref(2.0 * y, x)),
            None,
            "exact_ref(2y, x) at {}",
            args
        );
        // The scaled product rounds to 2y 2^128, and its error is not 0.
        let (qs, ys) = (3.0 * y * TWO_128, 2.0 * y * TWO_128);
        assert_eq!(qs * x, ys, "the scaled product at {}", args);
        assert_eq!(
            two_prod_err::<HAS_FMA>(qs, x, ys),
            -ys * pow2(-54),
            "the error of the product at {}",
            args
        );
        assert_eq!(atan2_near(y, x), 2.0 * y, "atan2({}) to nearest", args);
    }
    check_case(y, x, None, None);

    let exact = [(4, 1, 0.25), (4, 2, 0.5), (4, 3, 0.75), (12, 3, 0.25)];
    let mut found = 0;
    let mut false_positives = 0;
    for xb in [3, 5, (1 << 26) + 1, (3 << 30) + 1, (1 << 52) - 1, 4, 12] {
        for yb in [1, 3, 7, xb - 2, (1 << 51) + 1] {
            if yb >= xb {
                continue;
            }
            let (y, x) = (f64::from_bits(yb), f64::from_bits(xb));
            let quotient = exact
                .iter()
                .find(|&&(xe, ye, _)| xe == xb && ye == yb)
                .map(|&(_, _, q)| q);
            if quotient.is_some() {
                found += 1;
            } else {
                for y in [y, -y] {
                    assert_eq!(
                        (y / x).mul_add(x, -y),
                        0.0,
                        "the residual at {:e}, {:e}",
                        y,
                        x
                    );
                }
                false_positives += 1;
            }
            check_case(y, x, quotient, None);
        }
    }
    // Y = 1, 2 = X - 2 and 3 at X = 4, and Y = 3 at X = 12.
    assert_eq!(found, exact.len());
    assert!(false_positives > 0, "false positives {}", false_positives);
}

// The thresholds of `exact_div`, `tiny_quotient` and `midpoint_quotient`:
// - |y| in the 2 `f64`s on each side of 2^-968, where `exact_div` scales y below, with
//   x = X 2^f for odd X <= 63, with |y / x| near 2^t for t in {-1, -25, -26, -27, -60, -1021,
//   -1022, -1060, -1080}, around the pretests, `TINY_HYP` and `TINY_NEAR`, the midpoints and
//   the subnormals. The y on each side have odd parts Y with small odd factors (2^52 - 1 below
//   and 2^51 + 1 above), so that some quotients are `f64`s on both sides. At y = 2^-968 and
//   X = 1, y / x = 2^t, an `f64` for t >= -1074.
// - x in the 2 `f64`s on each side of 2^996, below which the rules call `exact_div`, with
//   y = x 2^-k for k in {26, 27, 28, 60, 1021, 1074, 1075}, at which y / x = 2^-k: an `f64` for
//   k <= 1074, which `tiny_quotient` gives for k >= 27, below `TINY_HYP`, and the midpoint
//   between 0 and 2^-1074 at k = 1075. Also the `f64`s next to those y.
// - y = q x for q in the 2 `f64`s on each side of `TINY_HYP` and `TINY_NEAR`, with x in {2^-990,
//   2^-960, 2^-940, 1, 2^995, 2^996}, so that |y| is on both sides of 2^-968 and x on both
//   sides of 2^996: `tiny_quotient` gives q below `TINY_HYP`, and `atan2_near` takes it, so
//   that no rounding test of the fast path runs (`fast_counts`), below `TINY_NEAR` only. Just
//   below `TINY_HYP`, atan q rounds to nearest to the `f64` before q.
// - the subnormal quotients 2^-1074, 2^-1073 and 5 2^-1074 (3 2^-1074 over 3 and 1.5, 15 2^-1074
//   over 3), (2^52 - 1) 2^-1074, the greatest, and the least normal one, 2^-1022, each with y
//   and x times 2^k for k
//   in {0, 1, 30, 995, 996}, and the quotients 2^-1075 and 3 2^-1075, which are not `f64`s
//   but midpoints (2^-1074 and 3 2^-1074 over 2, times the same 2^k up to 995).
// - subnormal x, 2^-1040 and 3 2^-1040, with y = 2^-1074 and 3 2^-1074.
#[test]
fn exact_div_thresholds() {
    // The exact quotients with |y| below 2^-968 and at or above it, and the y / x that
    // `tiny_quotient` gives with x below 2^996 and at or above it.
    let mut scales = [0; 2];
    let mut guards = [0; 2];
    for y in around(TWO_M968, 2) {
        for xo in (1..=63_u64).step_by(2) {
            let ex = 63 - xo.leading_zeros() as i32;
            for t in [-1, -25, -26, -27, -60, -1021, -1022, -1060, -1080] {
                let x = xo as f64 * pow2(-968 - t - ex);
                if y == TWO_M968 && xo == 1 {
                    let quotient = if t >= -1074 { Some(pow2(t)) } else { None };
                    check_case(y, x, quotient, None);
                } else {
                    check_refs(y, x);
                }
                if exact_ref(y, x).is_some() {
                    scales[usize::from(y >= TWO_M968)] += 1;
                }
            }
        }
    }
    for x in around(TWO_996, 2) {
        for k in [26, 27, 28, 60, 1021, 1074, 1075] {
            // x 2^-1000 and its product by 2^(1000 - k) are normal, and so exact.
            let y = x * pow2(-1000) * pow2(1000 - k);
            let quotient = if k <= 1074 { Some(pow2(-k)) } else { None };
            let midpoint = if k == 1075 { Some(0.0) } else { None };
            check_case(y, x, quotient, midpoint);
            for y1 in around(y, 1) {
                if y1 != y {
                    check_refs(y1, x);
                }
                if tiny_quotient(y1, x).is_some() {
                    guards[usize::from(x >= TWO_996)] += 1;
                }
            }
        }
    }
    assert!(
        scales.iter().chain(&guards).all(|&c| c > 0),
        "scales {:?}, guards {:?}",
        scales,
        guards
    );

    for q in [around(TINY_HYP, 2), around(TINY_NEAR, 2)].concat() {
        for x in [
            pow2(-990),
            pow2(-960),
            pow2(-940),
            1.0,
            pow2(995),
            pow2(996),
        ] {
            // q x is exact: the last bit of q is at least 2^-80, and so that of q x at least
            // 2^-1070.
            let y = q * x;
            check_case(y, x, Some(q), None);
            for y in [y, -y] {
                reset_fast_counts();
                atan2_near(y, x);
                let (passed, failed) = fast_counts();
                assert_eq!(
                    passed + failed == 0,
                    q < TINY_NEAR,
                    "atan2({:e}, {:e}) to nearest: {} rounding tests",
                    y,
                    x,
                    passed + failed
                );
            }
        }
    }
    let q = next_down(TINY_HYP);
    assert_eq!(atan2_near(q, 1.0), next_down(q));

    let quotients = [
        (3.0 * pow2(-1074), 3.0, pow2(-1074)),
        (3.0 * pow2(-1074), 1.5, pow2(-1073)),
        (15.0 * pow2(-1074), 3.0, 5.0 * pow2(-1074)),
        (
            f64::from_bits((1 << 52) - 1),
            1.0,
            f64::from_bits((1 << 52) - 1),
        ),
        (pow2(-1022), 1.0, pow2(-1022)),
    ];
    for (y, x, q) in quotients {
        for k in [0, 1, 30, 995, 996] {
            check_case(y * pow2(k), x * pow2(k), Some(q), None);
        }
    }
    for (y, f) in [(pow2(-1074), 0.0), (3.0 * pow2(-1074), pow2(-1074))] {
        for k in [0, 1, 30, 995] {
            check_case(y * pow2(k), 2.0 * pow2(k), None, Some(f));
        }
    }

    let (t, t3) = (pow2(-1074), 3.0 * pow2(-1074));
    let (x, x3) = (pow2(-1040), 3.0 * pow2(-1040));
    check_case(t, x, Some(pow2(-34)), None);
    check_case(t3, x, Some(3.0 * pow2(-34)), None);
    check_case(t, x3, None, None);
    check_case(t3, x3, Some(pow2(-34)), None);
}

// The midpoints m 2^-1075 for odd m < 2^53, at which `midpoint_quotient` gives (m - 1) 2^-1075
// with the sign of y, and `atan2_near` that too:
// - m = 1, at which that is +0 for y > 0 and -0 for y < 0: (2^-1074, 2), (3 2^-1074, 6),
//   (2^-80, 2^995), (2^-79, 2^996), at the guard, and (x 2^-1075, x) for x the `f64` before
//   2^996, the greatest x that `exact_div` takes;
// - m in {2^53 - 1, 2^53 - 3, 2^52 + 1}, the greatest odd m and two more, with x = 2^k for k in
//   {1, 995, 996};
// - 2y / x = q2 for q2 in the 3 `f64`s on each side of 2^-1021, with x = 2^k for k in {1, 60,
//   995, 996}: below 2^-1021, the bits of q2 are q2 / 2^-1074, and y / x = q2 / 2 is a midpoint
//   where they are odd, and an `f64` where they are even. At and above 2^-1021 y / x is an
//   `f64`, though the bits of the `f64` after 2^-1021 are odd;
// - even m in {2, 6, 2^52, 2^53 - 2}, at which y / x = (m / 2) 2^-1074 is an `f64`, with
//   x = 2^k and 3 2^k for the same k as q2.
#[test]
fn exact_div_midpoints() {
    let x = next_down(TWO_996);
    let ones = [
        (pow2(-1074), 2.0),
        (3.0 * pow2(-1074), 6.0),
        (pow2(-80), pow2(995)),
        (pow2(-79), pow2(996)),
        (x * pow2(-1050) * pow2(-25), x),
    ];
    for (y, x) in ones {
        check_case(y, x, None, Some(0.0));
        for (y, zero) in [(y, 0.0_f64), (-y, -0.0)] {
            let args = format!("{:e}, {:e}", y, x);
            assert_eq!(
                bits(midpoint_quotient(y, x)),
                Some(zero.to_bits()),
                "midpoint_quotient({})",
                args
            );
            assert_eq!(
                atan2_near(y, x).to_bits(),
                zero.to_bits(),
                "atan2({}) to nearest",
                args
            );
        }
    }
    for m in [(1_u64 << 53) - 1, (1 << 53) - 3, (1 << 52) + 1] {
        for k in [1, 995, 996] {
            // m < 2^53, and so exact, and so is its product by 2^(k - 1075) >= 2^-1074.
            let (y, x) = (m as f64 * pow2(k - 1075), pow2(k));
            check_case(y, x, None, Some(f64::from_bits((m - 1) / 2)));
        }
    }
    assert_eq!(next_up(TWO_M1021).to_bits() & 1, 1);
    for q2 in around(TWO_M1021, 3) {
        let b = q2.to_bits();
        let (quotient, midpoint) = if b >= 1 << 53 {
            (Some(q2 * 0.5), None)
        } else if b & 1 == 1 {
            (None, Some(f64::from_bits((b - 1) / 2)))
        } else {
            (Some(f64::from_bits(b / 2)), None)
        };
        for k in [1, 60, 995, 996] {
            check_case(q2 * pow2(k - 1), pow2(k), quotient, midpoint);
        }
    }
    for m in [2_u64, 6, 1 << 52, (1 << 53) - 2] {
        for xo in [1_u64, 3] {
            // y needs X m to be an `f64`, which 3 (2^53 - 2) is not.
            let ym = m * xo;
            if ym as f64 as u64 != ym {
                continue;
            }
            for k in [1, 60, 995, 996] {
                let (y, x) = (ym as f64 * pow2(k - 1075), xo as f64 * pow2(k));
                check_case(y, x, Some(f64::from_bits(m / 2)), None);
            }
        }
    }
}
