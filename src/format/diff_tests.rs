// Compares `bound` of `src/format.rs` with MPFR, through `fmt_bound_mpfr` of
// `src/mpfr_calls/mpfr.rs`, the MPFR call with which inari printed a bound of an interval
// before it had digits of its own: the text, byte for byte, in both directions, for the
// conversions `'f'`, `'e'` and `'a'`, without a precision and with the precisions 0 to 20, and
// on a sample of the numbers also with 40, 100, 330 and 1100. The numbers are random bit
// patterns, integers, numbers beside a decimal carry, numbers whose hex digits are at an edge,
// and `specials()`, each also negated. Whole intervals and decorated intervals go through
// `format!`, with and without a width and a precision, and are compared with the bounds from
// MPFR in the layout of `fmt_impl`. Their text is also parsed back: it has to parse and to
// contain the interval, and `{:x}` without a precision has to give the interval back exactly.
//
// MPFR's `%.0RUa` and `%.0RDa` of a number of at most 4 significant bits, rounded away from
// zero, add 1 to the digit though the number is exact, and write a NUL for the digit 16, where
// `bound` keeps the digit. `mpfr_bumps_exact` says which cases these are: there `check` asks
// that the texts differ, and the comparison of whole intervals skips them.
//
// The items that call MPFR are compiled only where the tests have it, on 64-bit Linux and
// macOS, by the `cfg` on each. `parse_back` and `exact_digit_at_precision_0` need no MPFR, so
// they also run where the tests have none, such as on wasm32 and i686.
//
// The number of random cases per generator can be set with `INARI_FORMAT_N`, and the cases
// changed with the seed `INARI_FORMAT_SEED`. Run with `--nocapture` to see the numbers of
// cases.

use super::bound;
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
use crate::mpfr_calls::mpfr::fmt_bound_mpfr;
use crate::{DecInterval, Decoration, Interval};
use std::fmt;

struct Rng(u64);

impl Rng {
    // SplitMix64.
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn coin(&mut self) -> bool {
        self.next() & 1 == 1
    }

    // An integer in `lo..=hi`.
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as u64) as i64
    }

    // `x` or `-x`.
    fn signed(&mut self, x: f64) -> f64 {
        if self.coin() {
            -x
        } else {
            x
        }
    }

    // An integer: a small one, one below 2^53, one beside a power of ten or one at or below a
    // power of two, or one of the `f64`s above 2^52, all of which are integers.
    fn integer(&mut self) -> f64 {
        let x = match self.below(5) {
            0 => self.range(0, 2000) as f64,
            1 => self.below(1 << 53) as f64,
            2 => {
                // 10^j is exact up to 10^22.
                let p: f64 = format!("1e{}", self.range(1, 22)).parse().unwrap();
                p + self.range(-3, 3) as f64
            }
            3 => {
                // 2^k, and the integers just below it, which are `f64`s apart from k >= 53.
                let k = self.range(0, 1023);
                let p = f64::from_bits(((k + 1023) as u64) << 52);
                if k <= 53 {
                    (p - self.below(4) as f64).max(0.0)
                } else {
                    f64::from_bits(p.to_bits() - self.below(4))
                }
            }
            _ => {
                // `m * 2^k` with 2^52 <= m < 2^53.
                let k = self.range(0, 971) as u64;
                f64::from_bits((1075 + k) << 52 | self.below(1 << 52))
            }
        };
        self.signed(x)
    }

    // A number beside `d * 10^j`, for a `d` of 1 to 17 digits: the nearest `f64`, or 1 to 3
    // ulps above or below it. `d` is often 99..9, a little below 10^p as `0.0996` is, or ends
    // in 5, so that the rounding at some precision carries into a new digit, or is a power of
    // ten.
    fn near_carry(&mut self) -> f64 {
        let p = self.range(1, 17) as u32;
        let pow = 10u64.pow(p);
        let d = match self.below(5) {
            0 => pow - 1,
            1 => pow.saturating_sub(self.range(2, 60) as u64).max(1),
            2 => self.below(pow / 10) * 10 + 5,
            3 => pow / 10,
            _ => pow / 10 + self.below(pow - pow / 10),
        };
        // Around the precisions of `{:.p}`, or anywhere in the range of `f64`.
        let j = if self.coin() {
            self.range(-40, 5)
        } else {
            self.range(-345, 308)
        };
        let x: f64 = format!("{}e{}", d, j).parse().unwrap();
        let x = x.min(f64::MAX);
        let y = f64::from_bits((x.to_bits() as i64 + self.range(-3, 3)) as u64);
        let x = if y.is_finite() && y.is_sign_positive() {
            y
        } else {
            x
        };
        self.signed(x)
    }

    // A number whose hex digits are at an edge, with the leading digit holding 1 to 4 bits:
    // all ones, at most 4 significant bits, a run of ones from the top followed by zeros, a
    // single 1 or random bits, so that the rounding at some precision carries into a new
    // digit, or a leading digit f. Subnormal numbers get the same shapes.
    fn hex_digits(&mut self) -> f64 {
        // A significand of 53 bits.
        let mut m: u64 = match self.below(5) {
            0 => (1 << 53) - 1,
            1 => (8 + self.below(8)) << 49,
            2 | 3 => {
                let l = self.range(1, 52) as u32;
                let low = (1u64 << (53 - l)) - 1;
                let rest = match self.below(3) {
                    0 => 0,
                    1 => 1,
                    _ => self.next() & low,
                };
                ((1u64 << 53) - 1 - low) | rest
            }
            _ => (1 << 52) | self.below(1 << 52),
        };
        // The exponent of the leading bit.
        let mut ex = match self.below(4) {
            0 => self.range(-1022, -1000),
            1 => self.range(1000, 1023),
            _ => self.range(-1022, 1023),
        };
        if self.below(4) == 0 {
            // A leading hex digit f: 4 leading ones, and 4 bits in the leading digit.
            m |= 0xf << 49;
            ex += 3 - ex.rem_euclid(4);
        }
        let x = if self.below(4) == 0 {
            // A subnormal number, `m >> s` times 2^-1074.
            f64::from_bits(m >> self.range(1, 52))
        } else {
            f64::from_bits(((ex + 1023) as u64) << 52 | (m & ((1 << 52) - 1)))
        };
        self.signed(x)
    }

    // A bound of an interval: an infinity, one of `specials()`, a number of one of the
    // generators above, or a random bit pattern.
    fn any(&mut self) -> f64 {
        match self.below(12) {
            0 => self.signed(f64::INFINITY),
            1 => {
                let xs = specials();
                xs[self.below(xs.len() as u64) as usize]
            }
            2 => self.integer(),
            3 | 4 => self.near_carry(),
            5 | 6 => self.hex_digits(),
            _ => loop {
                let x = f64::from_bits(self.next());
                if !x.is_nan() {
                    break x;
                }
            },
        }
    }

    // An interval with bounds from `any`: sometimes empty, entire, a point or one with a bound
    // of zero.
    fn interval(&mut self) -> Interval {
        match self.below(16) {
            0 => Interval::EMPTY,
            1 => Interval::ENTIRE,
            _ => {
                let a = self.any();
                let b = match self.below(4) {
                    0 => a,
                    1 => self.signed(0.0),
                    _ => self.any(),
                };
                let (a, b) = if a <= b { (a, b) } else { (b, a) };
                Interval::try_from((a, b)).unwrap_or(Interval::EMPTY)
            }
        }
    }

    // A decorated interval with any decoration, sometimes NaI.
    fn dec_interval(&mut self) -> DecInterval {
        use Decoration::*;
        let d = if self.below(16) == 0 {
            Ill
        } else {
            [Com, Dac, Def, Trv][self.below(4) as usize]
        };
        DecInterval::set_dec(self.interval(), d)
    }

    // A precision of 0 to 20, or sometimes one of `LARGE`.
    fn precision(&mut self) -> usize {
        if self.below(16) == 0 {
            LARGE[self.below(LARGE.len() as u64) as usize]
        } else {
            self.range(0, 20) as usize
        }
    }

    // A width that is often less than the length of a bound, and sometimes more.
    fn width(&mut self) -> usize {
        match self.below(4) {
            0 => self.range(0, 5) as usize,
            1 => 15,
            _ => self.range(0, 40) as usize,
        }
    }

    // A width and a precision for `format!`: neither, either or both.
    fn layouts(&mut self) -> [(Option<usize>, Option<usize>); 4] {
        [
            (None, None),
            (Some(self.width()), None),
            (None, Some(self.precision())),
            (Some(self.width()), Some(self.precision())),
        ]
    }
}

// The number of random cases per generator, which can be set with `INARI_FORMAT_N`.
fn n_cases() -> u64 {
    std::env::var("INARI_FORMAT_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(if cfg!(debug_assertions) { 100 } else { 1_000 })
}

// The random numbers of the generator numbered `gen`, which `INARI_FORMAT_SEED` changes.
fn rng(gen: u64) -> Rng {
    let seed = std::env::var("INARI_FORMAT_SEED")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0);
    Rng(seed.wrapping_add(gen << 32))
}

// ±0, ±2^-1074, `f64::MIN_POSITIVE` and the number below it, `f64::MAX`, 1, 0.5, 15, 31 and
// 32, and the negation of each.
fn specials() -> Vec<f64> {
    let xs = [
        0.0,
        5e-324,
        f64::MIN_POSITIVE,
        f64::from_bits(f64::MIN_POSITIVE.to_bits() - 1),
        f64::MAX,
        1.0,
        0.5,
        15.0,
        31.0,
        32.0,
    ];
    xs.iter().flat_map(|&x| [x, -x]).collect()
}

// The precisions that each number is printed with.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
fn precisions() -> Vec<Option<usize>> {
    let mut ps = vec![None];
    ps.extend((0..=20).map(Some));
    ps
}

// The larger precisions that a sample of the numbers is printed with. 1100 keeps every digit
// of every `f64` in each style.
const LARGE: [usize; 4] = [40, 100, 330, 1100];

// Whether MPFR's text of `x` adds 1 to the exact digit: for `%.0RUa` of a positive `x` and
// `%.0RDa` of a negative one, whose significand has at most 4 significant bits.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
fn mpfr_bumps_exact(x: f64, prec: Option<usize>, conv: char, up: bool) -> bool {
    if prec != Some(0) || conv != 'a' || x == 0.0 || !x.is_finite() || (x < 0.0) == up {
        return false;
    }
    let frac = x.to_bits() & ((1 << 52) - 1);
    let m = if x.abs() >= f64::MIN_POSITIVE {
        frac | 1 << 52
    } else {
        frac
    };
    64 - m.leading_zeros() - m.trailing_zeros() <= 4
}

// Compares `bound` with MPFR for `x`, and where `mpfr_bumps_exact` says that MPFR's digit is
// off, checks that the texts differ.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
fn check(x: f64, prec: Option<usize>, conv: char, up: bool, report: &mut Vec<String>) {
    let got = bound(x, prec, conv, up);
    let want = fmt_bound_mpfr(x, prec, conv, up);
    let bumps = mpfr_bumps_exact(x, prec, conv, up);
    if (got != want) != bumps {
        report.push(format!(
            "{:e} ({:#x}) prec {:?} conv {} up {}: got {:?}, MPFR {:?}, mpfr_bumps_exact {}",
            x,
            x.to_bits(),
            prec,
            conv,
            up,
            got,
            want,
            bumps
        ));
    }
}

// Compares `x` in every style, precision and direction.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
fn check_all(x: f64, report: &mut Vec<String>) {
    for conv in ['f', 'e', 'a'] {
        for prec in precisions() {
            for up in [false, true] {
                check(x, prec, conv, up, report);
            }
        }
    }
}

// Compares `x` in every style and direction, with the precisions of `LARGE`.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
fn check_large(x: f64, report: &mut Vec<String>) {
    for conv in ['f', 'e', 'a'] {
        for prec in LARGE {
            for up in [false, true] {
                check(x, Some(prec), conv, up, report);
            }
        }
    }
}

// `check_all`, and `check_large` for one case in 8.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
fn check_sampled(rng: &mut Rng, x: f64, report: &mut Vec<String>) {
    check_all(x, report);
    if rng.below(8) == 0 {
        check_large(x, report);
    }
}

// Runs the generator `gen` numbered `n` for `n_cases()` cases, and fails with the first
// mismatches if there are any.
fn run(name: &str, n: u64, mut gen: impl FnMut(&mut Rng, &mut Vec<String>)) {
    let mut rng = rng(n);
    let seed = rng.0;
    let cases = n_cases();
    let mut report = Vec::new();
    for _ in 0..cases {
        gen(&mut rng, &mut report);
    }
    eprintln!("format::diff_tests {}: {} cases", name, cases);
    assert!(
        report.is_empty(),
        "{}: {} mismatches with the seed {}, the first:\n{}",
        name,
        report.len(),
        seed,
        report[..report.len().min(10)].join("\n")
    );
}

// `x` as `format!` writes it in the style `conv`, with the width and the precision if they are
// `Some`.
fn text(
    x: impl fmt::Display + fmt::LowerExp + fmt::LowerHex,
    conv: char,
    width: Option<usize>,
    prec: Option<usize>,
) -> String {
    match (conv, width, prec) {
        ('f', None, None) => format!("{}", x),
        ('f', Some(w), None) => format!("{:w$}", x, w = w),
        ('f', None, Some(p)) => format!("{:.p$}", x, p = p),
        ('f', Some(w), Some(p)) => format!("{:w$.p$}", x, w = w, p = p),
        ('e', None, None) => format!("{:e}", x),
        ('e', Some(w), None) => format!("{:w$e}", x, w = w),
        ('e', None, Some(p)) => format!("{:.p$e}", x, p = p),
        ('e', Some(w), Some(p)) => format!("{:w$.p$e}", x, w = w, p = p),
        (_, None, None) => format!("{:x}", x),
        (_, Some(w), None) => format!("{:w$x}", x, w = w),
        (_, None, Some(p)) => format!("{:.p$x}", x, p = p),
        (_, Some(w), Some(p)) => format!("{:w$.p$x}", x, w = w, p = p),
    }
}

// The text of `x`, decorated with `d` if it is `Some`, as `text` should write it: the bounds
// from MPFR in the layout of `fmt_impl` of `src/format.rs`, or `None` where
// `mpfr_bumps_exact` holds for a bound. NaI is `Interval::EMPTY` with `Some(Decoration::Ill)`.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
fn want_text(
    x: Interval,
    d: Option<Decoration>,
    conv: char,
    width: Option<usize>,
    prec: Option<usize>,
) -> Option<String> {
    use Decoration::*;
    let w = width.unwrap_or(0);
    let sd = match d {
        Some(Com) => "_com",
        Some(Dac) => "_dac",
        Some(Def) => "_def",
        Some(Trv) => "_trv",
        _ => "",
    };
    // NaI, the empty interval and the entire one are centred in the width of the two bounds
    // and the comma.
    let special = if d == Some(Ill) {
        Some("nai")
    } else if x.is_empty() {
        Some("empty")
    } else if x.is_entire() {
        Some("entire")
    } else {
        None
    };
    if let Some(s) = special {
        return Some(format!("[{:^w$}]{}", s, sd, w = 2 * w + 1));
    }
    let (a, b) = (x.inf(), x.sup());
    if mpfr_bumps_exact(a, prec, conv, false) || mpfr_bumps_exact(b, prec, conv, true) {
        return None;
    }
    Some(format!(
        "[{:>w$},{:>w$}]{}",
        fmt_bound_mpfr(a, prec, conv, false),
        fmt_bound_mpfr(b, prec, conv, true),
        sd,
        w = w
    ))
}

// The bits of the bounds of `x`.
fn bits(x: Interval) -> (u64, u64) {
    (x.inf().to_bits(), x.sup().to_bits())
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
#[test]
fn edges() {
    let mut xs = vec![
        99.5,
        9.5,
        0.0996,
        1e23,
        0.1,
        std::f64::consts::PI,
        15.96875,
        0.9375,
    ];
    for i in 0..=1100 {
        xs.push(i as f64);
    }
    for j in -330..=310 {
        let y: f64 = format!("1e{}", j).parse().unwrap();
        for k in [1.0, 5.0, 9.0, 9.5, 9.95, 9.995] {
            let z = k * y;
            if z.is_finite() && z != 0.0 {
                xs.push(z);
                xs.push(f64::from_bits(z.to_bits() + 1));
                xs.push(f64::from_bits(z.to_bits() - 1));
            }
        }
    }
    let mut report = Vec::new();
    for x in xs.iter().flat_map(|&x| [x, -x]).chain(specials()) {
        check_all(x, &mut report);
        check_large(x, &mut report);
    }
    assert!(
        report.is_empty(),
        "{} mismatches, the first:\n{}",
        report.len(),
        report[..report.len().min(10)].join("\n")
    );
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
#[test]
fn random_bits() {
    run("random_bits", 1, |rng, report| {
        let x = f64::from_bits(rng.next());
        if !x.is_nan() {
            check_sampled(rng, x, report);
        }
    });
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
#[test]
fn integers() {
    run("integers", 2, |rng, report| {
        let x = rng.integer();
        check_sampled(rng, x, report);
    });
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
#[test]
fn near_carries() {
    run("near_carries", 3, |rng, report| {
        let x = rng.near_carry();
        check_sampled(rng, x, report);
    });
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
#[test]
fn hex_digits() {
    run("hex_digits", 4, |rng, report| {
        let x = rng.hex_digits();
        check_sampled(rng, x, report);
    });
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
#[test]
fn intervals_against_mpfr() {
    run("intervals_against_mpfr", 5, |rng, report| {
        let x = rng.interval();
        let dx = rng.dec_interval();
        for conv in ['f', 'e', 'a'] {
            for (width, prec) in rng.layouts() {
                let cases = [
                    (text(x, conv, width, prec), x, None),
                    (
                        text(dx, conv, width, prec),
                        dx.interval().unwrap_or(Interval::EMPTY),
                        Some(dx.decoration()),
                    ),
                ];
                for (got, x, d) in cases {
                    match want_text(x, d, conv, width, prec) {
                        Some(want) if got != want => report.push(format!(
                            "{:?} {:?} ({:#x?}) conv {} width {:?} prec {:?}: got {:?}, want {:?}",
                            x,
                            d,
                            bits(x),
                            conv,
                            width,
                            prec,
                            got,
                            want
                        )),
                        _ => {}
                    }
                }
            }
        }
    });
}

// Every text parses, as an `Interval` or a `DecInterval`, padded or not, to an interval that
// contains the one printed, with the same decoration, or `dac` for `com` where the text of a
// bound is beyond `f64::MAX`. `{:x}` without a precision gives the interval back exactly, a
// lower bound of zero included, which it writes as `-0x0p+0`.
#[test]
fn parse_back() {
    run("parse_back", 6, |rng, report| {
        let x = rng.interval();
        let dx = rng.dec_interval();
        for conv in ['f', 'e', 'a'] {
            for (width, prec) in rng.layouts() {
                let exact = conv == 'a' && prec.is_none();
                let s = text(x, conv, width, prec);
                let ok = match s.parse::<Interval>() {
                    Ok(y) => x.subset(y) && (!exact || bits(y) == bits(x)),
                    Err(_) => false,
                };
                let ok = ok
                    && (!exact
                        || matches!(crate::interval_exact!(&s), Ok(y) if bits(y) == bits(x)));
                if !ok {
                    report.push(format!(
                        "{:?} ({:#x?}) as {:?}: parses as {:?}, exactly as {:?}",
                        x,
                        bits(x),
                        s,
                        s.parse::<Interval>(),
                        crate::interval_exact!(&s)
                    ));
                }

                let s = text(dx, conv, width, prec);
                let ok = match (s.parse::<DecInterval>(), dx.interval()) {
                    (Ok(y), None) => y.is_nai(),
                    (Ok(y), Some(x)) => match y.interval() {
                        Some(z) => {
                            let (d, e) = (dx.decoration(), y.decoration());
                            x.subset(z)
                                && (!exact || bits(z) == bits(x))
                                && (e == d
                                    || (d == Decoration::Com
                                        && e == Decoration::Dac
                                        && !z.is_common_interval()))
                        }
                        None => false,
                    },
                    (Err(_), _) => false,
                };
                if !ok {
                    report.push(format!(
                        "{:?} as {:?}: parses as {:?}",
                        dx,
                        s,
                        s.parse::<DecInterval>()
                    ));
                }
            }
        }
    });
}

// Bounds on which `bound` and MPFR differ, as `(x, prec, conv, up)`, each with what it broke
// and where it was found.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
fn regressions() -> Vec<(f64, Option<usize>, char, bool)> {
    vec![
        // MPFR's `%.0RUa` of a positive bound, and `%.0RDa` of a negative one, of at most 4
        // significant bits adds 1 to the digit though the number is exact, and writes a NUL for
        // the digit 16 (the text after each is MPFR's): found by reading `vasprintf.c` of MPFR
        // 4.2.2 and confirmed by running it. `check` passes on these while MPFR's text differs
        // from ours.
        (1.0, Some(0), 'a', true),               // 0x9p-3
        (2.0, Some(0), 'a', true),               // 0x9p-2
        (15.0, Some(0), 'a', true),              // 0x, NUL, p+0
        (30.0, Some(0), 'a', true),              // 0x, NUL, p+1
        (-15.0, Some(0), 'a', false),            // -0x, NUL, p+0
        (0.9375, Some(0), 'a', true),            // 0x, NUL, p-4
        (-0.9375, Some(0), 'a', false),          // -0x, NUL, p-4
        (7.5, Some(0), 'a', true),               // 0x, NUL, p-1
        (0.5, Some(0), 'a', true),               // 0x9p-4
        (32.0, Some(0), 'a', true),              // 0x9p+2
        (-1.0, Some(0), 'a', false),             // -0x9p-3
        (5e-324, Some(0), 'a', true),            // 0x9p-1077
        (f64::MIN_POSITIVE, Some(0), 'a', true), // 0x9p-1025
    ]
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
#[test]
fn regressions_against_mpfr() {
    let mut report = Vec::new();
    for (x, prec, conv, up) in regressions() {
        check(x, prec, conv, up, &mut report);
    }
    assert!(report.is_empty(), "{}", report.join("\n"));
}

// Our text of the bounds of `regressions()` where MPFR's digit is off: the exact digit. MPFR
// writes `0x9p-3` for 1 rounded up, and `0x`, a NUL and `p+0` for 15 rounded up and for -15
// rounded down.
#[test]
fn exact_digit_at_precision_0() {
    for (x, want) in [
        (1.0, "0x8p-3"),
        (2.0, "0x8p-2"),
        (15.0, "0xfp+0"),
        (30.0, "0xfp+1"),
        (-15.0, "-0xfp+0"),
        (0.9375, "0xfp-4"),
        (-0.9375, "-0xfp-4"),
        (7.5, "0xfp-1"),
        (0.5, "0x8p-4"),
        (32.0, "0x8p+2"),
        (-1.0, "-0x8p-3"),
        (5e-324, "0x8p-1077"),
        (f64::MIN_POSITIVE, "0x8p-1025"),
    ] {
        // Both directions, as the bound is exact.
        for up in [false, true] {
            assert_eq!(bound(x, Some(0), 'a', up), want, "{:e} up {}", x, up);
        }
        let i = Interval::try_from((x, x)).unwrap();
        assert_eq!(format!("{:.0x}", i), format!("[{},{}]", want, want));
    }
}

// 65535, the largest precision that `format!` takes in recent Rust (older Rust takes any
// `usize`): the text of MPFR, of the length that each digit and the exponent take, and the
// same in both directions, as every `f64` is exact at it.
#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
#[test]
fn huge_precision() {
    let p = 65535;
    // The lengths for `'f'`, `'e'` and `'a'`.
    for (x, lens) in [
        (std::f64::consts::PI, [2 + p, 2 + p + 4, 4 + p + 3]),
        (f64::MAX, [310 + p, 2 + p + 5, 4 + p + 6]),
        (5e-324, [2 + p, 2 + p + 5, 4 + p + 6]),
    ] {
        for (conv, len) in ['f', 'e', 'a'].into_iter().zip(lens) {
            let s = bound(x, Some(p), conv, false);
            assert_eq!(s.len(), len, "{:e} conv {}", x, conv);
            assert!(bound(x, Some(p), conv, true) == s, "{:e} conv {}", x, conv);
            for up in [false, true] {
                assert!(
                    s == fmt_bound_mpfr(x, Some(p), conv, up),
                    "{:e} conv {} up {}",
                    x,
                    conv,
                    up
                );
            }
        }
        let i = Interval::try_from((-x, x)).unwrap();
        for (s, len) in [
            format!("{:.65535}", i),
            format!("{:.65535e}", i),
            format!("{:.65535x}", i),
        ]
        .into_iter()
        .zip(lens)
        {
            assert_eq!(s.len(), 2 * len + 4, "{:e}", x);
        }
    }
}
