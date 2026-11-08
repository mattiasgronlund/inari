// Throughput of `sin`, `cos` and `tan` of intervals with the selected backend, on N
// intervals of each of four classes (see `intervals`). The functions compute their bounds
// with inari's own kernel, so this benchmark needs no feature: `cargo bench --bench trig`.

use criterion::{
    criterion_group, criterion_main, BenchmarkId, Criterion, SamplingMode, Throughput,
};
use inari::Interval;
use std::f64::consts::FRAC_PI_2;
use std::hint::black_box;

const N: usize = 1024;

// Marsaglia's xorshift64 ("Xorshift RNGs", 2003), for deterministic inputs.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    // In [0, 1).
    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }

    // `x` or `-x`, with equal probability.
    fn sign(&mut self, x: f64) -> f64 {
        if self.next().is_multiple_of(2) {
            x
        } else {
            -x
        }
    }
}

// N intervals [a, b] of a class. The second bound is drawn less than a width `w` away from
// the first and then rounded, so `b - a` can reach `w` or exceed it by a rounding error:
// - "small": `a` in [-100, 100) and `w = 0.5`;
// - "narrow": the same with `w = 1e-9`, so that few contain a multiple of π/2;
// - "near": one bound within 3 ulps of `k * FRAC_PI_2` for an integer `0 < |k| <= 2^20`,
//   and `w = 1e-6`, where dividing the bounds by π or π/2 may not tell which side of the
//   multiple they are on;
// - "big": `|a|` between 2^30 and 2^50 and `w = 1`.
fn intervals(class: &str, seed: u64) -> Vec<Interval> {
    let mut rng = Rng(seed);
    (0..N)
        .map(|_| {
            let (a, b) = match class {
                "small" | "narrow" => {
                    let w = if class == "small" { 0.5 } else { 1e-9 };
                    let a = 100.0 * (2.0 * rng.unit() - 1.0);
                    (a, a + w * rng.unit())
                }
                "near" => {
                    let k = (rng.next() % (1 << 20) + 1) as f64;
                    let k = rng.sign(k);
                    // Adding to the bits of a float moves it away from zero by that many
                    // ulps, for either sign.
                    let d = (rng.next() % 7) as i64 - 3;
                    let e = f64::from_bits((k * FRAC_PI_2).to_bits().wrapping_add_signed(d));
                    let w = 1e-6 * rng.unit();
                    if rng.next().is_multiple_of(2) {
                        (e, e + w)
                    } else {
                        (e - w, e)
                    }
                }
                "big" => {
                    let a = 2f64.powf(30.0 + 20.0 * rng.unit());
                    let a = rng.sign(a);
                    (a, a + rng.unit())
                }
                _ => unreachable!(),
            };
            Interval::try_from((a, b)).unwrap()
        })
        .collect()
}

fn trig_bench(c: &mut Criterion) {
    let classes: Vec<(&str, Vec<Interval>)> = ["small", "narrow", "near", "big"]
        .into_iter()
        .zip(1..)
        .map(|(cl, seed)| (cl, intervals(cl, seed)))
        .collect();
    type Unary = fn(Interval) -> Interval;
    let fs: [(&str, Unary); 3] = [
        ("sin", Interval::sin),
        ("cos", Interval::cos),
        ("tan", Interval::tan),
    ];
    for (name, f) in fs {
        let mut g = c.benchmark_group(name);
        g.throughput(Throughput::Elements(N as u64));
        // An iteration takes milliseconds. Criterion's default, linear sampling runs the
        // routine 1 + 2 + ... + 100 times at least, which would take two to ten times the
        // default 5 s of measurement on the machine of BENCHMARKS.md; flat sampling runs it
        // the same number of times per sample.
        g.sampling_mode(SamplingMode::Flat);
        for (cl, x) in &classes {
            g.bench_function(BenchmarkId::from_parameter(cl), |b| {
                let mut out = vec![Interval::EMPTY; N];
                b.iter(|| {
                    for i in 0..N {
                        out[i] = f(black_box(x[i]));
                    }
                    black_box(&out);
                })
            });
        }
        g.finish();
    }
}

criterion_group!(benches, trig_bench);
criterion_main!(benches);
