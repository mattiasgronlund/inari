// Tests of the fast path of sin, cos and tan in the band: the x that the reductions give as
// N u + ρ with N mod 2048 = 0 and N != 0, within u/2 (1 + 2^-24) of the multiple N u of π/2.
// `fast_band` and `fast_tan_band` take those below `LIMIT`, from `fast_reduce` and
// `fast_band_reduce`, and `fast_band_big` and `fast_tan_band_big` those above it, from
// `fast_reduce_band_big`. `check_band_big` and `check_band_small` check the bounds of the
// reductions that `rocq/theories/FastTrigBandBig.v` and `rocq/theories/FastTrigBandRed.v`
// prove, and `check_fast` checks sin, cos and tan, at random arguments above `LIMIT`
// (`band_big_random`), at ±`KM` (`km_argument` and `mpfr::km_distance`) and at the ends of the
// band below and above `LIMIT` (`mpfr::band_edges`). `check_band_small` and the bounds that
// need π are checked only where the tests have MPFR. The arguments at and next to RN(k π/2)
// below `LIMIT` are those of `near_multiples`, `near_one_edge` and `mpfr::band_reductions` in
// `src/dyadic/trig/tests.rs`.

use super::*;

// `fast_reduce_band_big(x)` is `None` where `fast_reduce_big(x)` is not, and otherwise, where it
// is (n, rh, rl, rr), meets the conjuncts of `fast_reduce_band_big_correct` in
// `rocq/theories/FastTrigBandBig.v` that do not need π: x is finite with |x| >= `LIMIT`, n is in
// [0, 8191] with n mod 2048 = 0, rh, rl and rr are finite, rr = RN(rh + rl) and
// |rl| <= 2^-24 |rh|. With those that need π, 2^-61 <= |ρ| <= u/2 (1 + 2^-24) and
// |ρ - (rh + rl)| <= 2^-74 |ρ| for ρ = x - N u, they give 2^-62 < |rh| < 2^-11, which is checked
// too. On 64-bit Linux and macOS, where the tests have MPFR, `mpfr::check_band_big_bound`
// checks those that need π. Returns whether `fast_reduce_band_big` takes x.
fn check_band_big(x: f64) -> bool {
    let band = fast_reduce_band_big::<HAS_FMA>(x);
    assert!(
        fast_reduce_big::<HAS_FMA>(x).is_none() || band.is_none(),
        "fast_reduce_big({x:e}) and fast_reduce_band_big({x:e}) both take it"
    );
    let Some((n, rh, rl, rr)) = band else {
        return false;
    };
    assert!(
        x.is_finite()
            && x.abs() >= LIMIT
            && (0..8192).contains(&n)
            && n & 2047 == 0
            && rh.is_finite()
            && rl.is_finite()
            && rr.is_finite()
            && rr.to_bits() == (rh + rl).to_bits()
            && rl.abs() <= pow2(-24) * rh.abs()
            && pow2(-62) < rh.abs()
            && rh.abs() < pow2(-11),
        "fast_reduce_band_big({x:e}) = ({n}, {rh:e}, {rl:e}, {rr:e})"
    );
    #[cfg(all(
        target_pointer_width = "64",
        any(target_os = "linux", target_os = "macos")
    ))]
    mpfr::check_band_big_bound(x);
    true
}

// The twin of `check_band_big` for |x| < `LIMIT`: where the reduction (n, rh, rl, rr) of
// `fast_reduce` at x has n mod 2048 = 0 and n != 0, `fast_band_reduce(n, rh, rl)` =
// (sh, sl, sr) meets the conjuncts of `fast_band_reduce_correct` in
// `rocq/theories/FastTrigBandRed.v` that do not need π: sh, sl and sr are finite,
// sr = RN(sh + sl) and |sl| <= 2^-24 |sh|. With those that need π, 2^-61 <= |ρ| <=
// u/2 (1 + 2^-24) and |ρ - (sh + sl)| <= 2^-74 |ρ| for ρ = x - n u, they give
// 2^-62 < |sh| < 2^-11, which is checked too, and `mpfr::check_band_small_bound` checks those.
// Returns whether n mod 2048 = 0 and n != 0, where `fast_band` and `fast_tan_band` take x. Only
// `mpfr::band_edges` takes it, so it exists only where the tests have MPFR.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
fn check_band_small(x: f64) -> bool {
    let (n, rh, rl, _) = fast_reduce(x).unwrap();
    if n & 2047 != 0 || n == 0 {
        return false;
    }
    let (sh, sl, sr) = fast_band_reduce::<HAS_FMA>(n, rh, rl);
    assert!(
        sh.is_finite()
            && sl.is_finite()
            && sr.is_finite()
            && sr.to_bits() == (sh + sl).to_bits()
            && sl.abs() <= pow2(-24) * sh.abs()
            && pow2(-62) < sh.abs()
            && sh.abs() < pow2(-11),
        "fast_band_reduce({n}, {rh:e}, {rl:e}) = ({sh:e}, {sl:e}, {sr:e}) at {x:e}"
    );
    mpfr::check_band_small_bound(x);
    true
}

// The arguments of `fast_reduce_band_big` that `band_big_random` takes: x = m 2^(be - 1075) for
// the first 2 of random m in [2^52, 2^53) at which it takes x, at each biased exponent be from
// 1039 to 2046, from that of 2^16 to that of `f64::MAX`. It takes about 1 in 2048 of them, those
// with n mod 2048 = 0, and the draws at each be stop at 2^16, after which fewer than 2 takes have
// a chance below 10^-12. Each draw and its negation, taken or not, is checked as
// `check_band_big` checks it, so that `fast_reduce_big` and `fast_reduce_band_big` never both
// take one, and `fast_reduce_band_big` takes -x where it takes x.
fn band_big_args() -> Vec<f64> {
    let mut rng = Rng(1070);
    let mut v = vec![];
    for be in 1039..=2046 {
        let mut taken = 0;
        for _ in 0..1 << 16 {
            let x = from_parts(be, (1 << 52) + u128::from(rng.below(1 << 52)));
            let (pos, neg) = (check_band_big(x), check_band_big(-x));
            assert_eq!(pos, neg, "fast_reduce_band_big at ±{x:e}");
            if pos {
                v.push(x);
                taken += 1;
                if taken == 2 {
                    break;
                }
            }
        }
        assert_eq!(taken, 2, "biased exponent {be}");
    }
    v
}

// sin, cos and tan at the arguments of `band_big_args` and their negations, which the fast path
// takes before any rounding test (`answered`), as `check_fast` checks them. As ρ is spread over
// [-u/2, u/2] there, and so seldom small, most of the rounding tests pass, so that the fast path
// gives most of the results that `check_fast` compares.
#[test]
fn band_big_random() {
    let args = band_big_args();
    for &x in &args {
        assert!(answered(x) && answered(-x), "{x:e}");
    }
    for i in [SIN, COS, TAN] {
        reset_fast_counts();
        for &x in &args {
            check_fast(i, x);
            check_fast(i, -x);
        }
        let (passed, failed) = fast_counts();
        assert!(
            passed > 100 * failed && passed > 20_000,
            "{}: the rounding tests passed {passed} times and failed {failed} times",
            FUNCTIONS[i].0
        );
    }
}

// `KM` and -`KM`, the `f64`s closest to a multiple of π/2 other than 0 (the header of
// `trig.rs`), which `fast_reduce_big` declines: `fast_reduce_band_big` takes both, as
// `check_band_big` checks it, the fast paths of sin, cos and tan take both before any rounding
// test (`answered`), and sin, cos and tan there are as `check_fast` checks them.
#[test]
fn km_argument() {
    for x in [KM, -KM] {
        assert!(check_band_big(x) && answered(x), "{x:e}");
        for i in [SIN, COS, TAN] {
            check_fast(i, x);
        }
    }
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod mpfr {
    use super::*;
    use rug::{float::Constant, Float, Integer};

    // The precision of ρ = x - N u for |x| < 2^1024, as `BIG_PREC` in
    // `src/dyadic/trig/tests.rs`: x / u is below 2^1037, so that N, x / u rounded to an integer,
    // is right unless x / u is within about 2^-360 of a midpoint between two integers, and ρ,
    // from u and N u to 1,400 bits, is within about 2^-370 of x - N u.
    const BIG_PREC: u32 = 1400;

    // u = π/4096 to `BIG_PREC` bits.
    fn big_u() -> Float {
        Float::with_val(BIG_PREC, Constant::Pi) / 4096u32
    }

    // The conjuncts of `fast_band_reduce_correct` in `rocq/theories/FastTrigBandRed.v` and of
    // `fast_reduce_band_big_correct` in `rocq/theories/FastTrigBandBig.v` that need π, for
    // ρ = x - N u and the pair h + l that `what` gave at x: 2^-61 <= |ρ| <= u/2 (1 + 2^-24) and
    // |ρ - (h + l)| <= 2^-74 |ρ|. Returns |ρ| rounded to an `f64`.
    fn check_rho(what: &str, x: f64, k: &Integer, (h, l): (f64, f64)) -> f64 {
        let u = big_u();
        let mut half = Float::with_val(BIG_PREC, &u * (1.0 + pow2(-24)));
        half >>= 1;
        let rho = Float::with_val(BIG_PREC, x - Float::with_val(BIG_PREC, &u * k));
        let mut size = rho.clone();
        size.abs_mut();
        let mut err = Float::with_val(BIG_PREC, &rho - h);
        err -= l;
        err.abs_mut();
        let mut bound = size.clone();
        bound >>= 74;
        assert!(
            size >= pow2(-61) && size <= half && err <= bound,
            "{what}({x:e}): ({h:e}, {l:e}), with N = {k}, ρ = {:e} and |ρ - (h + l)| = {:e}",
            rho.to_f64(),
            err.to_f64()
        );
        size.to_f64()
    }

    // `fast_reduce_band_big(x)`, which takes x, meets the conjuncts of
    // `fast_reduce_band_big_correct` that need π with N = x / u rounded to an integer: n = N mod
    // 8192, N mod 2048 = 0 and those of `check_rho`. `fast_reduce_band_big` rounds R 2^-179,
    // which is within 2^-126 of x / u up to a multiple of 8192, so that its N is that one unless
    // x / u is that close to a midpoint between two integers, as `check_big_bound` of
    // `src/dyadic/trig/tests.rs` assumes for `fast_reduce_big` too. Returns |ρ| rounded to an
    // `f64`.
    pub(super) fn check_band_big_bound(x: f64) -> f64 {
        let (n, rh, rl, rr) = fast_reduce_band_big::<HAS_FMA>(x).unwrap();
        let k = Float::with_val(BIG_PREC, x / &big_u())
            .to_integer()
            .unwrap();
        assert!(
            k.mod_u(2048) == 0 && n == i64::from(k.mod_u(8192)),
            "fast_reduce_band_big({x:e}) = ({n}, {rh:e}, {rl:e}, {rr:e}), with N = {k}"
        );
        check_rho("fast_reduce_band_big", x, &k, (rh, rl))
    }

    // For an x that `check_band_small` takes, (sh, sl, sr) = `fast_band_reduce(n, rh, rl)` from
    // the reduction (n, rh, rl, rr) of `fast_reduce` at x meets the conjuncts of
    // `fast_band_reduce_correct` that need π, those of `check_rho` with N = n. Returns |ρ|
    // rounded to an `f64`.
    pub(super) fn check_band_small_bound(x: f64) -> f64 {
        let (n, rh, rl, _) = fast_reduce(x).unwrap();
        let (sh, sl, _) = fast_band_reduce::<HAS_FMA>(n, rh, rl);
        check_rho("fast_band_reduce", x, &Integer::from(n), (sh, sl))
    }

    // The arguments x = RN(k π/2 + s u/2 (1 + d)) for s = ±1 and d in {-2^-24, 0, 2^-24}, at the
    // ends of the band around k π/2, u/2 from it, where the n of the reductions goes from 2048 k
    // to 2048 k ± 1, and up to the u/2 (1 + 2^-24) that their bounds allow. d moves x by
    // 2^-24 u/2, about 2^-35.35, less than the spacing of the `f64`s from 2^17 up, where the
    // three d give the same x or adjacent ones. The small k are 2^j - 1, 2^j, 2^j + 1 and 3 2^j
    // for j >= 0, up to `LAST_K`, and `LAST_K`, so that x < `LIMIT`; at k = 0, where n is 0 or ±1,
    // no x is in the band. The big k are k0 + 5 to k0 + 8, for k0 the multiple of 4 nearest to
    // 1.5 2^e / (π/2) and e from 16 to 39, so that x >= `LIMIT`, past the k0 - 4 to k0 + 4 that
    // `big_steps` of `src/dyadic/trig/tests.rs` takes at 8 of these e.
    fn band_edge_args() -> Vec<f64> {
        let u = big_u();
        let mut ks: Vec<i64> = (0..16)
            .flat_map(|j| {
                let p = 1 << j;
                [p - 1, p, p + 1, 3 * p]
            })
            .filter(|&k| k <= LAST_K)
            .collect();
        ks.push(LAST_K);
        ks.sort_unstable();
        ks.dedup();
        let half_pi = Float::with_val(BIG_PREC, &u * 2048u32);
        for e in 16..=39 {
            let k0 = Float::with_val(BIG_PREC, 1.5 * pow2(e) / &half_pi) / 4u32;
            let k0 = k0.to_integer().unwrap().to_i64().unwrap() * 4;
            ks.extend(k0 + 5..=k0 + 8);
        }
        let mut v = vec![];
        for k in ks {
            let ku = Float::with_val(BIG_PREC, &u * (2048 * k));
            for s in [-1.0, 1.0] {
                for d in [-pow2(-24), 0.0, pow2(-24)] {
                    let mut off = Float::with_val(BIG_PREC, &u * (s * (1.0 + d)));
                    off >>= 1;
                    v.push(Float::with_val(BIG_PREC, &ku + &off).to_f64());
                }
            }
        }
        v
    }

    // sin, cos and tan at the arguments of `band_edge_args`, the `f64` on each side of each and
    // the negations of all, as `check_fast` checks them. The fast paths take every one of them
    // before any rounding test (`answered`): those in the band, where `check_band_small` or
    // `check_band_big` checks the reduction, and the others, where |ρ| is above 2^-13, far from
    // the rh = 0 at which `fast_quad` and `fast_tan` decline x and the |rh| < 2^-65 at which
    // `fast_reduce_big` does. Both occur below `LIMIT` and above it. Below `LIMIT`, x / u is close
    // to n + 1/2, where `fast_reduce` may round it to either neighbour, and `check_band_small`
    // checks |ρ| <= u/2 (1 + 2^-24) for its n, not that n is x / u rounded. Above it,
    // `check_band_big` checks that too, as `fast_reduce_band_big` rounds x / u to within 2^-126.
    #[test]
    fn band_edges() {
        // counts[b][c]: how many arguments below `LIMIT` (b = 0) and above it (b = 1) are outside
        // the band (c = 0) and in it (c = 1).
        let mut counts = [[0usize; 2]; 2];
        for x in band_edge_args() {
            for y in around(x, 1) {
                for z in [y, -y] {
                    let big = z.abs() >= LIMIT;
                    let band = if big {
                        check_band_big(z)
                    } else {
                        check_band_small(z)
                    };
                    counts[usize::from(big)][usize::from(band)] += 1;
                    assert!(answered(z), "{z:e}");
                    for i in [SIN, COS, TAN] {
                        check_fast(i, z);
                    }
                }
            }
        }
        assert!(counts.iter().flatten().all(|&c| c > 0), "{counts:?}");
    }

    // At ±`KM`, 2^-61 <= |ρ| < 2^-60: the least |ρ| that `check_rho` allows, the 2^-61 of
    // `km_distance` in `rocq/theories/KahanMcDonald.v`, is within a factor of 2 of |ρ| there,
    // about 2^-60.89.
    #[test]
    fn km_distance() {
        for x in [KM, -KM] {
            let rho = check_band_big_bound(x);
            assert!(rho < pow2(-60), "{x:e}: |ρ| = {rho:e}");
        }
    }
}
