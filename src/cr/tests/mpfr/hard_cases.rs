// The functions of `src/cr.rs` against MPFR at hard-to-round arguments: a sample, in
// `hard_cases.wc` next to this file, of the worst-case files `src/binary64/<f>/<f>.wc` of
// CORE-MATH (https://gitlab.inria.fr/core-math/core-math). The header of `hard_cases.wc` states
// the rule that picked the sample and keeps CORE-MATH's MIT notice. `hard_cases` checks the
// three roundings at each argument as `compare` does, and prints, with `--nocapture`, the
// levels of Ziv's strategy that the kernel used for each function and rounding, and how many
// rounding tests of the fast paths (those of exp, exp2, exp10, sinh, cosh and tanh) passed and
// failed. Level 0 means that the kernel returned without Ziv's strategy: a rule gave the
// result, a fast path passed its rounding test, or the function is cbrt or hypot, which the
// kernel computes from exact integer roots. The ignored `full_hard_cases` does the same at
// every argument of the files of a clone of CORE-MATH, `random_levels` at random arguments,
// and `sample_hard_cases` writes the sample again from a clone of CORE-MATH. Where a fast path
// passed, `hard_cases` (alone) checks the argument again with the fast paths disabled, so that
// Ziv's strategy is checked there too.

use super::*;
use crate::dyadic::{fast_counts, reset_fast_counts, reset_ziv_level, set_fast_path, ziv_level};
use rug::{float::Round, ops::PowAssignRound};
use std::{cmp::Ordering, collections::HashSet, fmt::Write as _};

// The sample. A line `@ <name> <file>` starts the arguments of the function `<name>` of
// `FILES`, which come from CORE-MATH's `src/binary64/<file>`. The other lines are CORE-MATH's:
// `#` comments, and arguments, one or two separated by a comma, as `parse` reads them, with
// anything after a `#` a comment.
const SAMPLE: &str = include_str!("hard_cases.wc");

// The functions of the sample, those of `UNARY` in its order but sqrt, which CORE-MATH has no
// file for, then atan2, pow and hypot, each with the name of its directory and file in
// CORE-MATH's `src/binary64`. A function of `UNARY` has the same index in both. cbrt.wc is
// complete up to scaling by powers of 8, as cbrt(8x) = 2 cbrt(x): it has every argument of
// three adjacent binades at which cbrt has at least 44 identical bits after the round bit, and
// every one in [1, 8) at which cbrt is exact. hypot.wc, of two arguments, is not complete.
const FILES: [(&str, &str); 22] = [
    ("exp", "exp"),
    ("exp2", "exp2"),
    ("exp10", "exp10"),
    ("ln", "log"),
    ("log2", "log2"),
    ("log10", "log10"),
    ("sinh", "sinh"),
    ("cosh", "cosh"),
    ("tanh", "tanh"),
    ("asinh", "asinh"),
    ("acosh", "acosh"),
    ("atanh", "atanh"),
    ("sin", "sin"),
    ("cos", "cos"),
    ("tan", "tan"),
    ("asin", "asin"),
    ("acos", "acos"),
    ("atan", "atan"),
    ("cbrt", "cbrt"),
    ("atan2", "atan2"),
    ("pow", "pow"),
    ("hypot", "hypot"),
];

// The `f64` that `s` names, rounded to nearest, ties to even, as C's `strtod` reads it: a
// hexadecimal float such as `-0x1.62e42fefa39efp+9`, `0x.fffffffffffffp-1022` or `0x1`, a
// decimal such as `-1000.0`, `inf`, `nan` or `snan` (a signalling NaN), each with an optional
// sign. A few lines of CORE-MATH have more bits than an `f64`, such as `0x11.e44c76af19d67p+1`
// in tanh.wc.
fn parse(s: &str) -> f64 {
    let (neg, t) = match s.as_bytes().first() {
        Some(b'-') => (true, &s[1..]),
        Some(b'+') => (false, &s[1..]),
        _ => (false, s),
    };
    let v = if let Some(h) = t.strip_prefix("0x") {
        parse_hex(h).unwrap_or_else(|| panic!("cannot parse {s}"))
    } else if t == "snan" {
        f64::from_bits(0x7ff4_0000_0000_0000)
    } else {
        t.parse().unwrap_or_else(|_| panic!("cannot parse {s}"))
    };
    if neg {
        -v
    } else {
        v
    }
}

// The `f64` nearest m 2^e, ties to even, where m is the integer of the hexadecimal digits of
// `s` = `<digits>p<e'>` or `<digits>` (e' = 0) and e = e' - 4k for k digits after the point,
// or `None` if it overflows or `s` is not of that form.
fn parse_hex(s: &str) -> Option<f64> {
    let (digits, exp) = s.split_once('p').unwrap_or((s, "0"));
    let mut e: i64 = exp.parse().ok()?;
    let mut m = 0u128;
    let mut after_point = false;
    for c in digits.chars() {
        if c == '.' {
            after_point = true;
            continue;
        }
        m = m.checked_mul(16)?.checked_add(c.to_digit(16)? as u128)?;
        if after_point {
            e -= 4;
        }
    }
    if m == 0 {
        return Some(0.0);
    }
    // Rounds away the `drop` low bits of m that an `f64` cannot hold, as it has 53 bits and
    // none below 2^-1074. Then m <= 2^53 and m 2^e is an `f64` unless it overflows.
    let drop = (128 - m.leading_zeros() as i64 - 53).max(-1074 - e).max(0);
    if drop >= 128 {
        return None;
    } else if drop > 0 {
        let (q, rem, half) = (m >> drop, m & ((1 << drop) - 1), 1 << (drop - 1));
        m = q + (rem > half || (rem == half && q & 1 == 1)) as u128;
        e += drop;
        if m == 0 {
            // m 2^e was at most 2^-1075, the tie between 0 and 2^-1074, which goes to 0.
            return Some(0.0);
        }
    }
    // m odd.
    e += m.trailing_zeros() as i64;
    m >>= m.trailing_zeros();
    // m 2^e is in [2^top, 2^(top + 1)).
    let top = e + 127 - m.leading_zeros() as i64;
    if top > 1023 {
        None
    } else if top >= -1022 {
        // A normal `f64`: the biased exponent and the 52 bits below the leading one.
        let frac = (m << (52 - (top - e))) as u64 & ((1 << 52) - 1);
        Some(f64::from_bits(((top + 1023) as u64) << 52 | frac))
    } else if e >= -1074 {
        // A subnormal `f64`, (m 2^(e + 1074)) 2^-1074 with m 2^(e + 1074) < 2^52.
        Some(f64::from_bits((m << (e + 1074)) as u64))
    } else {
        None
    }
}

// The arguments of a line of the sample or of a CORE-MATH file, if it has any. Each argument
// is the first word of its part of the line: three lines of sin.wc, such as
// `0x1.4f1d73be27a31p+1 44`, end in a number without a `#`.
fn args(line: &str) -> Option<Vec<f64>> {
    let data = line.split('#').next().unwrap_or("").trim();
    (!data.is_empty()).then(|| {
        data.split(',')
            .map(|a| parse(a.split_whitespace().next().unwrap_or("")))
            .collect()
    })
}

// The levels of Ziv's strategy that the kernel used for a function in one rounding, over the
// arguments of the sample: the number of arguments at each level, 0, 1, 2, 4, ..., 64 limbs as
// `ziv_level` gives them, the first argument at the highest level, the number of failed
// rounding tests, and the arguments at the cap, 64 limbs. `fast` counts the rounding tests of
// the fast paths that passed and failed, as `fast_counts` gives them.
#[derive(Default)]
struct Levels {
    count: [usize; 8],
    first_at_max: String,
    failed: usize,
    capped: Vec<String>,
    fast: [usize; 2],
}

const LEVELS: [usize; 8] = [0, 1, 2, 4, 8, 16, 32, 64];

impl Levels {
    // Records `ziv_level()` and `fast_counts()` at `args`.
    fn record(&mut self, args: &str) {
        let (passed, failed) = fast_counts();
        self.fast[0] += passed;
        self.fast[1] += failed;
        let (level, failed) = ziv_level();
        let i = LEVELS.iter().position(|&l| l == level).unwrap();
        if self.count[i..].iter().all(|&n| n == 0) {
            self.first_at_max = args.to_string();
        }
        self.count[i] += 1;
        self.failed += failed;
        if level == 64 {
            self.capped.push(args.to_string());
        }
    }

    fn max(&self) -> usize {
        LEVELS[self.top().unwrap_or(0)]
    }

    // The index in `LEVELS` of the highest level, if any argument is recorded.
    fn top(&self) -> Option<usize> {
        self.count.iter().rposition(|&n| n > 0)
    }

    // Adds `other`, recorded at arguments that come after those of `self`.
    fn merge(&mut self, other: Levels) {
        // `None < Some(_)`, so an empty `self` takes the first argument of `other`.
        if other.top() > self.top() {
            self.first_at_max = other.first_at_max;
        }
        for (n, m) in self.count.iter_mut().zip(other.count) {
            *n += m;
        }
        self.failed += other.failed;
        self.capped.extend(other.capped);
        for (n, m) in self.fast.iter_mut().zip(other.fast) {
            *n += m;
        }
    }
}

// Prints, for each function of `FILES` and each rounding, the highest level in `levels` (in
// the order of `FILES`), the first argument at it, the number of arguments at each level, the
// number of failed rounding tests and, for a function that took a fast path, the numbers of
// its rounding tests that passed and failed, then the arguments at the cap. `of` names the
// arguments.
fn print_levels(of: &str, levels: &[[Levels; 3]]) {
    println!("The highest level of Ziv's strategy, in limbs, over {of}");
    println!("(and the first argument at it; arguments per level; failed rounding tests;");
    println!("rounding tests of the fast path passed/failed, if it was taken):");
    for ((name, _), lv) in FILES.iter().zip(levels) {
        for (r, l) in ["rn", "rd", "ru"].iter().zip(lv) {
            let mut per_level = String::new();
            for (level, count) in LEVELS.iter().zip(l.count) {
                if count > 0 {
                    write!(per_level, " {level}:{count}").unwrap();
                }
            }
            let mut fast = String::new();
            if l.fast != [0, 0] {
                write!(fast, "; fast {}/{}", l.fast[0], l.fast[1]).unwrap();
            }
            println!(
                "{name}_{r}: {} ({}; {}; {}{fast})",
                l.max(),
                l.first_at_max,
                per_level.trim_start(),
                l.failed
            );
        }
    }
    let capped: Vec<String> = FILES
        .iter()
        .zip(levels)
        .flat_map(|((name, _), lv)| {
            ["rn", "rd", "ru"]
                .iter()
                .zip(lv)
                .flat_map(move |(r, l)| l.capped.iter().map(move |a| format!("{name}_{r}({a})")))
        })
        .collect();
    println!("At the cap, 64 limbs: {}", capped.len());
    for c in &capped {
        println!("  {c}");
    }
}

// `[g(0), g(1), g(2)]`, the three roundings of a function at `args`, with the levels that
// `ziv` used for `g(r)`, and the rounding tests of the fast paths, recorded in `levels[r]`.
fn measured(levels: &mut [Levels; 3], args: &str, g: impl Fn(usize) -> f64) -> [f64; 3] {
    let mut got = [0.0; 3];
    for (r, (v, l)) in got.iter_mut().zip(levels).enumerate() {
        reset_ziv_level();
        reset_fast_counts();
        *v = g(r);
        l.record(args);
    }
    got
}

type F2 = fn(f64, f64) -> f64;

// atan2, pow and hypot in their three roundings, then MPFR's.
const ATAN2: ([F2; 3], [F2; 3]) = (
    [atan2_rn, atan2_rd, atan2_ru],
    [oracle::atan2_rn, oracle::atan2_rd, oracle::atan2_ru],
);
const POW: ([F2; 3], [F2; 3]) = (
    [pow_rn, pow_rd, pow_ru],
    [oracle::pow_rn, oracle::pow_rd, oracle::pow_ru],
);
const HYPOT: ([F2; 3], [F2; 3]) = (
    [hypot_rn, hypot_rd, hypot_ru],
    [oracle::hypot_rn, oracle::hypot_rd, oracle::hypot_ru],
);

// The function `FILES[k]` at `xs`, written `text`, against MPFR in the three roundings, as
// `compare` does, with the levels that the kernel used recorded in `levels`.
fn check(errs: &mut Vec<String>, levels: &mut [Levels; 3], k: usize, xs: &[f64], text: &str) {
    let name = FILES[k].0;
    let (got, want) = match (name, xs) {
        ("atan2", &[y, x]) => (
            measured(levels, text, |r| ATAN2.0[r](y, x)),
            ATAN2.1.map(|g| g(y, x)),
        ),
        ("pow", &[x, y]) => (
            measured(levels, text, |r| POW.0[r](x, y)),
            POW.1.map(|g| g(x, y)),
        ),
        ("hypot", &[x, y]) => (
            measured(levels, text, |r| HYPOT.0[r](x, y)),
            HYPOT.1.map(|g| g(x, y)),
        ),
        (_, &[x]) if k < UNARY.len() && UNARY[k].0 == name => {
            let (_, cr, mpfr) = UNARY[k];
            (measured(levels, text, |r| cr[r](x)), mpfr.map(|g| g(x)))
        }
        _ => panic!("{name}({text}) has the wrong number of arguments"),
    };
    compare(errs, name, text, got, want);
}

// `check` at each of `entries`, arguments of `FILES[k]` with their text, split over 16
// threads: the levels that the kernel used, and the mismatches with MPFR in the order of
// `entries`.
fn check_all(k: usize, entries: &[(Vec<f64>, String)]) -> ([Levels; 3], Vec<String>) {
    // (`div_ceil` needs Rust 1.73, and the `msrv` job of CI checks the tests with Rust 1.65.)
    let chunk = ((entries.len() + 15) / 16).max(1);
    // Each thread records its own levels, as `ziv_level` gives those of its thread.
    let parts: Vec<([Levels; 3], Vec<String>)> = std::thread::scope(|s| {
        let threads: Vec<_> = entries
            .chunks(chunk)
            .map(|part| {
                s.spawn(move || {
                    let mut levels = Default::default();
                    let mut errs = vec![];
                    for (xs, text) in part {
                        check(&mut errs, &mut levels, k, xs, text);
                    }
                    (levels, errs)
                })
            })
            .collect();
        threads
            .into_iter()
            .map(|t| t.join().unwrap_or_else(|e| std::panic::resume_unwind(e)))
            .collect()
    });
    // Merged in the order of the parts, so that the first argument at the highest level is the
    // first of `entries`.
    let mut levels: [Levels; 3] = Default::default();
    let mut errs = vec![];
    for (lv, es) in parts {
        for (l, p) in levels.iter_mut().zip(lv) {
            l.merge(p);
        }
        errs.extend(es);
    }
    (levels, errs)
}

// The functions at the arguments of the sample against MPFR, bit for bit, or a NaN where MPFR
// gives one, in the three roundings, and again with the fast paths disabled where one passed.
// Prints the levels that the kernel used.
#[test]
fn hard_cases() {
    let mut errs = vec![];
    let mut levels: Vec<[Levels; 3]> = FILES.iter().map(|_| Default::default()).collect();
    let mut f = None;
    let mut total = 0;
    let mut again = 0;
    let fast_passed = |lv: &[Levels; 3]| lv.iter().map(|l| l.fast[0]).sum::<usize>();
    for line in SAMPLE.lines() {
        if let Some(rest) = line.strip_prefix("@ ") {
            let name = rest.split(' ').next().unwrap();
            f = Some(FILES.iter().position(|&(n, _)| n == name).unwrap());
            continue;
        }
        let Some(xs) = args(line) else { continue };
        let k = f.expect("an argument before the first `@` line");
        let text = line.split('#').next().unwrap().trim();
        let before = fast_passed(&levels[k]);
        check(&mut errs, &mut levels[k], k, &xs, text);
        total += 1;
        // Where a fast path gave a result, Ziv's strategy did not run: check it there too.
        // `set_fast_path` acts on this thread, the one that `check` computes on.
        if fast_passed(&levels[k]) > before {
            let mut off = vec![];
            let mut scratch: [Levels; 3] = Default::default();
            set_fast_path(false);
            check(&mut off, &mut scratch, k, &xs, text);
            set_fast_path(true);
            // A disabled fast path counts as neither passed nor failed.
            assert!(scratch.iter().all(|l| l.fast == [0, 0]));
            errs.extend(off.into_iter().map(|e| e + " (fast paths disabled)"));
            again += 1;
        }
    }
    assert!(total > 0, "the sample is empty");
    print_levels(&format!("the {total} arguments of the sample"), &levels);
    println!("Checked again with the fast paths disabled: {again} arguments");
    report(errs);
}

// `hard_cases` at every argument of the files of the clone of CORE-MATH at `$CORE_MATH`, after
// repeated arguments are removed: `CORE_MATH=<clone> cargo test --release --lib
// full_hard_cases -- --ignored --nocapture`. It takes some minutes on 16 threads.
#[test]
#[ignore]
fn full_hard_cases() {
    let root = std::env::var("CORE_MATH").expect("CORE_MATH, a clone of CORE-MATH");
    let mut errs = vec![];
    let mut levels = vec![];
    let mut total = 0;
    for (k, (name, file)) in FILES.iter().enumerate() {
        let start = std::time::Instant::now();
        let path = format!("{root}/src/binary64/{file}/{file}.wc");
        let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let mut seen = HashSet::new();
        let entries: Vec<(Vec<f64>, String)> = src
            .lines()
            .filter_map(|line| {
                let xs = args(line)?;
                let bits: Vec<u64> = xs.iter().map(|x| x.to_bits()).collect();
                let text = line.split('#').next().unwrap().trim().to_string();
                seen.insert(bits).then_some((xs, text))
            })
            .collect();
        let (lv, es) = check_all(k, &entries);
        eprintln!(
            "{name}: {} arguments, {} mismatches, {:.1} s",
            entries.len(),
            es.len(),
            start.elapsed().as_secs_f64()
        );
        total += entries.len();
        levels.push(lv);
        errs.extend(es);
    }
    print_levels(
        &format!("the {total} arguments of CORE-MATH's files"),
        &levels,
    );
    report(errs);
}

// The number of random arguments (pairs of arguments for atan2, pow and hypot) of each function
// in `random_levels`.
const RANDOM: usize = 1_000_000;

// `hard_cases` at `RANDOM` random arguments of each function, x and y from `Rng::arg` except y
// of pow from `Rng::exponent`, as in `unary_random`, `atan2_special_and_random` and
// `pow_special_and_random` of `src/cr.rs`, with other seeds: `cargo test --release --lib
// random_levels -- --ignored --nocapture`.
#[test]
#[ignore]
fn random_levels() {
    let mut errs = vec![];
    let mut levels = vec![];
    for (k, (name, _)) in FILES.iter().enumerate() {
        let mut rng = Rng(100 + k as u64);
        let entries: Vec<(Vec<f64>, String)> = (0..RANDOM)
            .map(|_| {
                let xs = match *name {
                    "atan2" | "hypot" => vec![rng.arg(), rng.arg()],
                    "pow" => vec![rng.arg(), rng.exponent()],
                    _ => vec![rng.arg()],
                };
                let text: Vec<String> = xs.iter().map(|x| format!("{x:e}")).collect();
                (xs, text.join(", "))
            })
            .collect();
        let (lv, es) = check_all(k, &entries);
        levels.push(lv);
        errs.extend(es);
    }
    print_levels(
        &format!("{RANDOM} random arguments of each function"),
        &levels,
    );
    report(errs);
}

// How hard a value v = f(x) is to round to an `f64`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Hard {
    // v is a NaN, an infinity, 0, or at least 2^1024.
    Special,
    // 2^(-h-1) <= d / |v| < 2^-h with h < `NEAR`, where d is the distance from v to the
    // nearest `f64` or midpoint of two adjacent `f64`s, the subnormals among them.
    H(i32),
    // The same with h >= `NEAR`, or v rounded to 256 bits is one of those and v is not: mostly
    // at tiny arguments, where f(x) is about 1, x or a constant.
    Near,
    // v is an `f64` or the midpoint of two adjacent `f64`s.
    Exact,
}

// Where `Hard::Near` starts. The worst cases of the files have at most about 70 identical bits
// after the round bit, h <= 124 or so, and 160 leaves room for h to be computed exactly from v
// at 256 bits.
const NEAR: i32 = 160;

// f(xs) of the function `name` of `FILES` by MPFR, rounded to nearest at 256 bits, and how
// hard it is to round.
fn hardness(name: &str, xs: &[f64]) -> Hard {
    let n = Round::Nearest;
    let mut v = Float::with_val(256, xs[0]);
    let dir = match name {
        "exp" => v.exp_round(n),
        "exp2" => v.exp2_round(n),
        "exp10" => v.exp10_round(n),
        "ln" => v.ln_round(n),
        "log2" => v.log2_round(n),
        "log10" => v.log10_round(n),
        "sinh" => v.sinh_round(n),
        "cosh" => v.cosh_round(n),
        "tanh" => v.tanh_round(n),
        "asinh" => v.asinh_round(n),
        "acosh" => v.acosh_round(n),
        "atanh" => v.atanh_round(n),
        "sin" => v.sin_round(n),
        "cos" => v.cos_round(n),
        "tan" => v.tan_round(n),
        "asin" => v.asin_round(n),
        "acos" => v.acos_round(n),
        "atan" => v.atan_round(n),
        "cbrt" => v.cbrt_round(n),
        "atan2" => v.atan2_round(&Float::with_val(53, xs[1]), n),
        "pow" => v.pow_assign_round(&Float::with_val(53, xs[1]), n),
        "hypot" => v.hypot_round(&Float::with_val(53, xs[1]), n),
        _ => unreachable!("{name}"),
    };
    if !v.is_normal() || v.get_exp().unwrap() > 1024 {
        return Hard::Special;
    }
    // |v| is in [2^(e-1), 2^e), where the `f64`s are the multiples of 2^q, and the midpoints
    // the odd multiples of 2^(q-1).
    let q = (v.get_exp().unwrap() - 53).max(-1074);
    let a = Float::with_val(256, v.abs_ref());
    // The bits of |v| below 2^(q-1), as a number in [0, 1), and its distance to 0 or 1: d in
    // units of 2^(q-1). Both are exact, as `fract` and `- 1` need at most the 256 bits of |v|.
    let frac = (a.clone() << (1 - q)).fract();
    let d = if frac < 0.5 { frac } else { -(frac - 1u32) };
    if d.is_zero() {
        return if dir == Ordering::Equal {
            Hard::Exact
        } else {
            Hard::Near
        };
    }
    // d / |v| = r 2^(q-1) with r in [2^(g-1), 2^g), g its exponent.
    let r = Float::with_val(64, &d / &a);
    let h = -(r.get_exp().unwrap() + q - 1);
    if h < NEAR {
        Hard::H(h)
    } else {
        Hard::Near
    }
}

// The rule that picks the sample from each file, after repeated arguments are removed, with
// ties going to the first in the file: of a function of one `f64`, every argument that is not
// a hexadecimal float (CORE-MATH's special values), the first `EXACT_1` arguments at which f is
// `Hard::Exact` and the first `EXACT_1` at which it is `Hard::Near`, the `HARDEST_1` with the
// highest h, the one with the highest h in each section (a run of comments and the arguments
// after it, mostly one search), and the one with the highest h in each of `SLICES` slices of
// equal size of the hexadecimal arguments sorted by value. Of atan2, pow and hypot, the same
// without the special values and the slices, with `EXACT_2` and `HARDEST_2`.
const EXACT_1: usize = 8;
const HARDEST_1: usize = 40;
const SLICES: usize = 16;
const EXACT_2: usize = 4;
const HARDEST_2: usize = 24;

// An argument line of a CORE-MATH file.
struct Entry {
    text: String,
    xs: Vec<f64>,
    hex: bool,
    hard: Hard,
}

// Of the entries `idx`, the first with the highest h.
fn hardest(entries: &[Entry], idx: impl Iterator<Item = usize>) -> Option<usize> {
    let mut best: Option<(i32, usize)> = None;
    for i in idx {
        if let Hard::H(h) = entries[i].hard {
            if best.map_or(true, |(b, _)| h > b) {
                best = Some((h, i));
            }
        }
    }
    best.map(|(_, i)| i)
}

// Writes the sample to `$HARD_CASES_OUT` from the clone of CORE-MATH at `$CORE_MATH`:
// `CORE_MATH=<clone> HARD_CASES_OUT=<file> cargo test --release --lib sample_hard_cases --
// --ignored`. It takes some minutes on 16 threads.
#[test]
#[ignore]
fn sample_hard_cases() {
    let root = std::env::var("CORE_MATH").expect("CORE_MATH, a clone of CORE-MATH");
    let out_path = std::env::var("HARD_CASES_OUT").expect("HARD_CASES_OUT, the file to write");
    let commit = std::process::Command::new("git")
        .args(["-C", &root, "rev-parse", "HEAD"])
        .output()
        .expect("git");
    let commit = String::from_utf8(commit.stdout).unwrap();
    let mut licence: Option<Vec<String>> = None;
    let mut body = String::new();
    for (name, file) in FILES {
        let path = format!("{root}/src/binary64/{file}/{file}.wc");
        let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let lines: Vec<&str> = src.lines().collect();
        // Every file starts with the same 20 lines of CORE-MATH's notice.
        let head: Vec<String> = lines[..20].iter().map(|l| l.to_string()).collect();
        assert!(head[0].starts_with("# This file is part of the CORE-MATH project"));
        assert_eq!(*licence.get_or_insert_with(|| head.clone()), head, "{path}");
        // The sections: each one's comments and its entries.
        let mut sections: Vec<(Vec<&str>, Vec<usize>)> = vec![];
        let mut entries = vec![];
        let mut seen = HashSet::new();
        for line in &lines[20..] {
            let new_section = sections.last().map_or(true, |(_, es)| !es.is_empty());
            if line.starts_with('#') {
                if new_section {
                    sections.push((vec![], vec![]));
                }
                sections.last_mut().unwrap().0.push(line);
                continue;
            }
            let Some(xs) = args(line) else { continue };
            if !seen.insert(xs.iter().map(|x| x.to_bits()).collect::<Vec<_>>()) {
                continue;
            }
            if sections.is_empty() {
                sections.push((vec![], vec![]));
            }
            let text = line.split('#').next().unwrap().trim().to_string();
            let hex = text.split(',').all(|a| {
                let a = a.trim().trim_start_matches(['+', '-']);
                a.starts_with("0x")
            });
            sections.last_mut().unwrap().1.push(entries.len());
            entries.push(Entry {
                text,
                xs,
                hex,
                hard: Hard::Special,
            });
        }
        // MPFR, on 16 threads. (`div_ceil` needs Rust 1.73, and the `msrv` job of CI checks
        // the tests with Rust 1.65.)
        let chunk = ((entries.len() + 15) / 16).max(1);
        std::thread::scope(|s| {
            for part in entries.chunks_mut(chunk) {
                s.spawn(move || {
                    for e in part {
                        e.hard = hardness(name, &e.xs);
                    }
                });
            }
        });
        let unary = !matches!(name, "atan2" | "pow" | "hypot");
        let (n_exact, n_hardest) = if unary {
            (EXACT_1, HARDEST_1)
        } else {
            (EXACT_2, HARDEST_2)
        };
        let mut pick = vec![false; entries.len()];
        if unary {
            for (p, e) in pick.iter_mut().zip(&entries) {
                *p |= !e.hex;
            }
        }
        for kind in [Hard::Exact, Hard::Near] {
            let of_kind = (0..entries.len()).filter(|&i| entries[i].hard == kind);
            for i in of_kind.take(n_exact) {
                pick[i] = true;
            }
        }
        let mut by_h: Vec<(i32, usize)> = (0..entries.len())
            .filter_map(|i| match entries[i].hard {
                Hard::H(h) => Some((-h, i)),
                _ => None,
            })
            .collect();
        by_h.sort_unstable();
        for &(_, i) in by_h.iter().take(n_hardest) {
            pick[i] = true;
        }
        for (_, es) in &sections {
            if let Some(i) = hardest(&entries, es.iter().copied()) {
                pick[i] = true;
            }
        }
        if unary {
            let mut by_value: Vec<usize> = (0..entries.len()).filter(|&i| entries[i].hex).collect();
            by_value.sort_by(|&i, &j| entries[i].xs[0].total_cmp(&entries[j].xs[0]));
            let size = ((by_value.len() + SLICES - 1) / SLICES).max(1);
            for slice in by_value.chunks(size) {
                if let Some(i) = hardest(&entries, slice.iter().copied()) {
                    pick[i] = true;
                }
            }
        }
        writeln!(body, "@ {name} {file}/{file}.wc").unwrap();
        for (comments, es) in &sections {
            if !es.iter().any(|&i| pick[i]) {
                continue;
            }
            for c in comments {
                writeln!(body, "{c}").unwrap();
            }
            for &i in es.iter().filter(|&&i| pick[i]) {
                let e = &entries[i];
                let h = match e.hard {
                    Hard::Special => "special".to_string(),
                    Hard::Exact => "exact".to_string(),
                    Hard::Near => "near".to_string(),
                    Hard::H(h) => format!("h={h}"),
                };
                writeln!(body, "{} # {h}", e.text).unwrap();
            }
        }
        let max_h = by_h.first().map_or(0, |&(h, _)| -h);
        let picked = pick.iter().filter(|&&p| p).count();
        let count = |kind| entries.iter().filter(|e| e.hard == kind).count();
        eprintln!(
            "{name}: {} arguments ({} exact, {} near), {picked} picked, highest h {max_h}",
            entries.len(),
            count(Hard::Exact),
            count(Hard::Near)
        );
    }
    let mut out = String::new();
    for line in [
        "# A sample of the worst cases of CORE-MATH, for the test `hard_cases` in hard_cases.rs:",
        "# of its files src/binary64/<f>/<f>.wc at https://gitlab.inria.fr/core-math/core-math,",
    ] {
        writeln!(out, "{line}").unwrap();
    }
    writeln!(out, "# commit {}.", commit.trim()).unwrap();
    let rule = format!(
        "\
# A line `@ <name> <file>` starts the arguments of the function <name> of `inari::cr`, from
# CORE-MATH's <file>. The other lines are CORE-MATH's: arguments, one per line, or two
# separated by a comma, each after the comments of the section of its file that it comes
# from (a run of comments and the arguments after it, mostly one search). After each argument,
# a comment says how hard f(x) is to round, by MPFR at 256 bits: `h=<h>` where
# 2^(-h-1) <= d/|f(x)| < 2^-h with h < {NEAR}, d the distance from f(x) to the nearest f64 or
# midpoint of two adjacent f64s, subnormals included (for a normal f(x), h is 53 or 54 plus
# the number of identical bits after the round bit); `near` where h >= {NEAR} (mostly tiny
# arguments, where f(x) is about 1, x or a constant); `exact` where f(x) is one of those
# numbers; and `special` where f(x) is a NaN, an infinity, 0 or at least 2^1024.
#
# The rule that picked them from each file, after repeated arguments are removed, with ties
# going to the first in the file: of a function of one f64, every argument that is not a
# hexadecimal float (CORE-MATH's special values), the first {EXACT_1} exact ones and the first
# {EXACT_1} near ones, the {HARDEST_1} with the highest h, the one with the highest h in each
# section, and the one with the highest h in each of {SLICES} slices of equal size of the
# hexadecimal arguments sorted by value; of atan2, pow and hypot, the first {EXACT_2} exact ones
# and the first {EXACT_2} near ones, the {HARDEST_2} with the highest h, and the one with the
# highest h in each section. The ignored test `sample_hard_cases` in hard_cases.rs writes
# this file again.
#
# The worst-case files of CORE-MATH carry this notice, kept here:
"
    );
    out.push_str(&rule);
    for l in licence.unwrap() {
        writeln!(out, "{l}").unwrap();
    }
    out.push_str(&body);
    std::fs::write(&out_path, out).unwrap_or_else(|e| panic!("{out_path}: {e}"));
}
