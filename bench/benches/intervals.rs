// Throughput of interval operations with the selected backend, on N intervals of
// each sign class: P (positive), N (negative) and M (containing zero).

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use inari::Interval;
use std::hint::black_box;

const N: usize = 1024;

// 2^-1010 (biased exponent 1023 - 1010 = 13). The product of an interval scaled by
// it and one in [1, 3) lies below 2^-968, where the FMA backend's multiplication
// leaves its fast path, but is still normal.
const TINY: f64 = f64::from_bits(13 << 52);

// Deterministic values in [1, 2).
fn values(seed: u64, n: usize) -> Vec<f64> {
    let mut s = seed;
    (0..n)
        .map(|_| {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            1.0 + (s >> 11) as f64 / (1u64 << 53) as f64
        })
        .collect()
}

// Intervals with endpoints in [1, 3) times `scale`, a power of two, so that the
// scaling is exact.
fn intervals(class: char, seed: u64, scale: f64) -> Vec<Interval> {
    values(seed, 2 * N)
        .chunks(2)
        .map(|c| {
            let (a, b) = (c[0].min(c[1]), c[0].max(c[1]) + 1.0);
            let (a, b) = (a * scale, b * scale);
            let (a, b) = match class {
                'P' => (a, b),
                'N' => (-b, -a),
                'M' => (-a, b),
                _ => unreachable!(),
            };
            Interval::try_from((a, b)).unwrap()
        })
        .collect()
}

// The first operand of each pair is scaled by `x_scale`, the second is not.
fn bench_binary(
    c: &mut Criterion,
    name: &str,
    f: fn(Interval, Interval) -> Interval,
    classes: &[&str],
    x_scale: f64,
) {
    let mut g = c.benchmark_group(name);
    g.throughput(Throughput::Elements(N as u64));
    for cl in classes {
        let mut it = cl.chars();
        let x = intervals(it.next().unwrap(), 1, x_scale);
        let y = intervals(it.next().unwrap(), 2, 1.0);
        g.bench_function(BenchmarkId::from_parameter(cl), |b| {
            let mut out = vec![Interval::EMPTY; N];
            b.iter(|| {
                for i in 0..N {
                    out[i] = f(black_box(x[i]), black_box(y[i]));
                }
                black_box(&out);
            })
        });
    }
    g.finish();
}

fn horner(x: Interval) -> Interval {
    // An arbitrary polynomial of degree 8 with point coefficients.
    const C: [f64; 9] = [1.0, -0.5, 0.25, -0.125, 0.0625, 0.75, -1.5, 3.0, -2.0];
    let mut acc = Interval::try_from((C[8], C[8])).unwrap();
    for &c in C[..8].iter().rev() {
        acc = acc * x + Interval::try_from((c, c)).unwrap();
    }
    acc
}

fn det3(m: &[Interval; 9]) -> Interval {
    m[0] * (m[4] * m[8] - m[5] * m[7]) - m[1] * (m[3] * m[8] - m[5] * m[6])
        + m[2] * (m[3] * m[7] - m[4] * m[6])
}

fn intervals_bench(c: &mut Criterion) {
    let all = ["PP", "PN", "PM", "NP", "NN", "NM", "MP", "MN", "MM"];
    bench_binary(c, "add", |x, y| x + y, &["PP", "PM", "MM"], 1.0);
    bench_binary(c, "sub", |x, y| x - y, &["PP", "PM", "MM"], 1.0);
    bench_binary(c, "mul", |x, y| x * y, &all, 1.0);
    // Products between 2^-1010 and 2^-1006 (see `TINY`). Most of the products in
    // operations recorded from rcad, a CAD kernel, were below 2^-968 too.
    bench_binary(c, "mul_tiny", |x, y| x * y, &all, TINY);
    // x / y for y ∌ 0; division by an interval containing zero is also included.
    bench_binary(c, "div", |x, y| x / y, &["PP", "PN", "MP", "NN", "PM"], 1.0);

    let mut g = c.benchmark_group("unary");
    g.throughput(Throughput::Elements(N as u64));
    let p = intervals('P', 3, 1.0);
    let m = intervals('M', 4, 1.0);
    type Unary = fn(Interval) -> Interval;
    // sqrt/M is the case that does not use the vector square root: an interval
    // containing zero needs the square root of one endpoint only.
    let unary: [(&str, Unary, &[Interval]); 4] = [
        ("sqrt/P", Interval::sqrt, &p),
        ("sqrt/M", Interval::sqrt, &m),
        ("horner8/P", horner, &p),
        ("horner8/M", horner, &m),
    ];
    for (name, f, x) in unary {
        g.bench_function(name, |b| {
            let mut out = vec![Interval::EMPTY; N];
            b.iter(|| {
                for i in 0..N {
                    out[i] = f(black_box(x[i]));
                }
                black_box(&out);
            })
        });
    }
    // Matrices with a third of the entries in M and the rest in P.
    let ms: Vec<[Interval; 9]> = (0..N)
        .map(|i| {
            let mut e = [Interval::EMPTY; 9];
            for (j, e) in e.iter_mut().enumerate() {
                let src = if (i + j) % 3 == 0 { &m } else { &p };
                *e = src[(i * 9 + j) % N];
            }
            e
        })
        .collect();
    g.bench_function("det3/mixed", |b| {
        let mut out = vec![Interval::EMPTY; N];
        b.iter(|| {
            for i in 0..N {
                out[i] = det3(black_box(&ms[i]));
            }
            black_box(&out);
        })
    });
    g.finish();
}

criterion_group!(benches, intervals_bench);
criterion_main!(benches);
