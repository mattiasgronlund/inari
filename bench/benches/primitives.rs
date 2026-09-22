// Throughput and latency of the rounding primitives of the selected backend.
//
// Throughput: N independent operations. Latency: a chain of N operations, each of
// which depends on the result of the previous one. All inputs are normal numbers
// of moderate magnitude, so the generic backend always takes its fast paths.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use inari::__bench::*;
use std::hint::black_box;

const N: usize = 1024;

// Deterministic values in ±[1, 2).
fn values(seed: u64, n: usize) -> Vec<f64> {
    let mut s = seed;
    (0..n)
        .map(|_| {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let x = 1.0 + (s >> 11) as f64 / (1u64 << 53) as f64;
            if s & 1 == 0 {
                x
            } else {
                -x
            }
        })
        .collect()
}

fn vectors(seed: u64) -> Vec<F64X2> {
    values(seed, 2 * N)
        .chunks(2)
        .map(|c| constant(c[0], c[1]))
        .collect()
}

fn bench_binary(c: &mut Criterion, name: &str, f: fn(F64X2, F64X2) -> F64X2, k: F64X2) {
    let x = vectors(1);
    let y = vectors(2);
    let mut g = c.benchmark_group(name);
    g.throughput(Throughput::Elements(N as u64));
    g.bench_function(BenchmarkId::new("throughput", N), |b| {
        let mut out = vec![constant(0.0, 0.0); N];
        b.iter(|| {
            for i in 0..N {
                out[i] = f(black_box(x[i]), black_box(y[i]));
            }
            black_box(&out);
        })
    });
    g.bench_function(BenchmarkId::new("latency", N), |b| {
        b.iter(|| {
            let mut acc = constant(1.0, 1.5);
            for _ in 0..N {
                acc = f(acc, black_box(k));
            }
            black_box(acc)
        })
    });
    g.finish();
}

fn primitives(c: &mut Criterion) {
    // The constants of the latency chains keep the values bounded.
    bench_binary(c, "add_ru", add_ru, constant(1e-3, 1e-3));
    bench_binary(c, "mul_ru", mul_ru, constant(1.0 - 1e-6, 1.0 + 1e-6));
    bench_binary(c, "div_ru", div_ru, constant(1.0 + 1e-6, 1.0 - 1e-6));

    let (x, y, z) = (vectors(1), vectors(2), vectors(3));
    let mut g = c.benchmark_group("mul_add_ru");
    g.throughput(Throughput::Elements(N as u64));
    g.bench_function(BenchmarkId::new("throughput", N), |b| {
        let mut out = vec![constant(0.0, 0.0); N];
        b.iter(|| {
            for i in 0..N {
                out[i] = mul_add_ru(black_box(x[i]), black_box(y[i]), black_box(z[i]));
            }
            black_box(&out);
        })
    });
    g.bench_function(BenchmarkId::new("latency", N), |b| {
        let (k, l) = (constant(0.75, 0.625), constant(1.0, 1.5));
        b.iter(|| {
            let mut acc = constant(1.0, 1.5);
            for _ in 0..N {
                acc = mul_add_ru(acc, black_box(k), black_box(l));
            }
            black_box(acc)
        })
    });
    g.finish();

    let x: Vec<f64> = values(4, N).iter().map(|x| x.abs()).collect();
    let mut g = c.benchmark_group("sqrt1_ru");
    g.throughput(Throughput::Elements(N as u64));
    g.bench_function(BenchmarkId::new("throughput", N), |b| {
        let mut out = vec![0.0; N];
        b.iter(|| {
            for i in 0..N {
                out[i] = sqrt1_ru(black_box(x[i]));
            }
            black_box(&out);
        })
    });
    g.bench_function(BenchmarkId::new("latency", N), |b| {
        b.iter(|| {
            let mut acc = 3.0;
            for _ in 0..N {
                // √(acc + 3) stays in [1, 3).
                acc = sqrt1_ru(acc + black_box(3.0));
            }
            black_box(acc)
        })
    });
    g.finish();
}

criterion_group!(benches, primitives);
criterion_main!(benches);
