// Tests of the limb loops, against references that are written out bit by bit, so that they run
// on every platform, without MPFR. The outputs and the scratch of each call of `shl_into` and
// `div_rem` hold garbage before it, all ones and then random limbs, so that a limb of an output
// that the call leaves unwritten shows, and most likely a limb of the scratch that it reads
// before it writes it.

use super::*;

struct Rng(u64);

impl Rng {
    // SplitMix64, as in `src/dyadic/tests.rs`.
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

    // A limb that is often 0, 1, 2^63 or all ones, to make carries and borrows run across
    // limbs.
    fn limb(&mut self) -> u64 {
        match self.below(8) {
            0 => 0,
            1 => 1,
            2 => 1 << 63,
            3 | 4 => u64::MAX,
            _ => self.next(),
        }
    }

    // `len` limbs from `limb`.
    fn limbs(&mut self, len: usize) -> Vec<u64> {
        (0..len).map(|_| self.limb()).collect()
    }

    // Two slices of `len` limbs of garbage, for an output or a scratch: all ones, and random.
    fn garbage(&mut self, len: usize) -> [Vec<u64>; 2] {
        [vec![u64::MAX; len], (0..len).map(|_| self.next()).collect()]
    }
}

// Bit `i` of the number that `x` holds, which is 0 past its end.
fn bit(x: &[u64], i: u64) -> u64 {
    match x.get((i / 64) as usize) {
        Some(l) => l >> (i % 64) & 1,
        None => 0,
    }
}

// Whether x < y for the numbers that `x` and `y` hold, a limb past the end being 0.
fn less(x: &[u64], y: &[u64]) -> bool {
    let limb = |x: &[u64], i: usize| x.get(i).copied().unwrap_or(0);
    for i in (0..x.len().max(y.len())).rev() {
        if limb(x, i) != limb(y, i) {
            return limb(x, i) < limb(y, i);
        }
    }
    false
}

// `x` with zero limbs on top, to `len` limbs.
fn padded(x: &[u64], len: usize) -> Vec<u64> {
    let mut x = x.to_vec();
    x.resize(len, 0);
    x
}

// `(x << sh) mod 2^(64 n)` in `n` limbs, bit by bit: bit `i` is bit `i - sh` of `x` for
// sh <= i < 64 n, and 0 below `sh`.
fn shl_ref(x: &[u64], sh: u64, n: usize) -> Vec<u64> {
    let mut out = vec![0; n];
    for i in sh..64 * n as u64 {
        out[(i / 64) as usize] |= bit(x, i - sh) << (i % 64);
    }
    out
}

// `shl_into` of 0 to 6 limbs into 1 to 5, so that the input is shorter or longer than the
// output, by shifts within a limb, of whole limbs and across them, to the last bit of the
// output and past it, where all of it is 0, and by random shifts below 7 limbs.
#[test]
fn shl_into_bit_by_bit() {
    let mut rng = Rng(1);
    for n in 1..=5 {
        let bits = 64 * n as u64;
        for len in 0..=6 {
            for _ in 0..16 {
                let x = rng.limbs(len);
                let mut shifts = vec![
                    0,
                    1,
                    63,
                    64,
                    65,
                    127,
                    128,
                    bits - 1,
                    bits,
                    bits + 1,
                    u64::MAX,
                ];
                shifts.extend((0..8).map(|_| rng.below(64 * 7)));
                for sh in shifts {
                    let want = shl_ref(&x, sh, n);
                    for mut out in rng.garbage(n) {
                        shl_into(&mut out, &x, sh);
                        assert_eq!(out, want, "{:x?} << {} in {} limbs", x, sh, n);
                    }
                }
            }
        }
    }
}

// `(x / d, x % d)` in `x.len()` and `d.len()` limbs, for d > 0, by restoring division, a bit at
// a time: from the top bit of `x` down, r := 2 r + that bit, and where r >= d, r := r - d and
// that bit of the quotient is 1. As r < d before each step, 2 r + 1 < 2 d fits d.len() + 1
// limbs, and the top one of them is 0 at the end.
fn div_rem_ref(x: &[u64], d: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let mut q = vec![0; x.len()];
    let mut r = vec![0; d.len() + 1];
    for i in (0..64 * x.len() as u64).rev() {
        let mut carry = bit(x, i);
        for l in &mut r {
            let top = *l >> 63;
            *l = *l << 1 | carry;
            carry = top;
        }
        if !less(&r, d) {
            let mut borrow = false;
            for (k, l) in r.iter_mut().enumerate() {
                let (t, b1) = l.overflowing_sub(d.get(k).copied().unwrap_or(0));
                let (t, b2) = t.overflowing_sub(u64::from(borrow));
                *l = t;
                borrow = b1 | b2;
            }
            q[(i / 64) as usize] |= 1 << (i % 64);
        }
    }
    assert_eq!(r.pop(), Some(0));
    (q, r)
}

// `div_rem` gives what `div_rem_ref` does, into a quotient, a remainder and a scratch of the
// lengths that it asks for, the scratch exactly x.len() + d.len() + 2 limbs, which hold garbage.
// Returns the quotient.
fn check_div_rem(rng: &mut Rng, x: &[u64], d: &[u64]) -> Vec<u64> {
    let want = div_rem_ref(x, d);
    let [q0, q1] = rng.garbage(x.len());
    let [r0, r1] = rng.garbage(d.len());
    let [s0, s1] = rng.garbage(x.len() + d.len() + 2);
    for (mut q, mut r, mut scratch) in [(q0, r0, s0), (q1, r1, s1)] {
        div_rem(&mut q, &mut r, x, d, &mut scratch);
        assert_eq!((q, r), want, "{:x?} / {:x?}", x, d);
    }
    want.0
}

// Dividends for the divisor `d`, whose top nonzero limb is limb `n - 1`. Below `d`, which
// `div_rem` answers before it divides: 0, a number of fewer limbs than `n`, and d - 1 in `n`
// limbs and with zero limbs on top, up to two more than `d` has. Then `d` in `n` limbs and in
// one more than `d` has, the multiples k d for `k` of one and two limbs, with a zero limb on top
// and without, k d + d - 1 below the next multiple, and numbers of 0 to 7 random limbs.
fn dividends(rng: &mut Rng, d: &[u64]) -> Vec<Vec<u64>> {
    let n = d.iter().rposition(|&l| l != 0).unwrap() + 1;
    let mut d_1 = d.to_vec();
    assert!(!sub_assign(&mut d_1, &[1], false));
    let shorter = rng.below(n as u64) as usize;
    let mut xs = vec![
        vec![],
        rng.limbs(shorter),
        d_1[..n].to_vec(),
        padded(&d_1, d.len() + 2),
        d[..n].to_vec(),
        padded(d, d.len() + 1),
    ];
    for k in [vec![1], vec![2], vec![u64::MAX], rng.limbs(1), rng.limbs(2)] {
        let mut x = vec![0; d.len() + k.len()];
        mul_into(&mut x, d, &k);
        xs.push(padded(&x, x.len() + 1));
        xs.push(x.clone());
        // k d + d - 1 < (k + 1) d <= B^(d.len() + k.len()), for B = 2^64.
        assert!(!add_assign(&mut x, &d_1));
        xs.push(x);
    }
    for len in 0..=7 {
        xs.push(rng.limbs(len));
    }
    xs
}

// `div_rem` by divisors d = d1 * B^j of 1 to 6 limbs, for B = 2^64, with j = 0 or more zero
// limbs at the bottom, which `div_rem` strips, and zero limbs at the top or none: d1 of one
// limb, which takes a division by a limb, or of 2 to 6, which takes Algorithm D. The top limb
// of d1 is 1, 2 or a random one below B/2, which D1 shifts, or B/2 or B - 1, which it does not.
#[test]
fn div_rem_bit_by_bit() {
    let mut rng = Rng(2);
    for len in 1..=6 {
        for j in 0..len {
            for mid in 1..=len - j {
                for _ in 0..4 {
                    let s = rng.below(63) + 1;
                    for top in [1, 2, rng.next() >> s | 1, 1 << 63, u64::MAX] {
                        let mut d = vec![0; j];
                        d.extend(rng.limbs(mid - 1));
                        d.push(top);
                        d.resize(len, 0);
                        for x in dividends(&mut rng, &d) {
                            check_div_rem(&mut rng, &x, &d);
                        }
                    }
                }
            }
        }
    }
}

// Divisions in which the estimate of a quotient limb after D3 is 1 too large, so that D6 adds
// the divisor back, as in `div_rem_add_back` in `src/nat.rs`: for
// v = w * B^(m - 2) + low with `w` of 2 limbs, its top limb at least B/2, and
// 0 < low < B^(m - 2), the quotient of u = q0 * w * B^(m - 2) by `v` is q0 - 1 for 1 < q0 < B,
// as 0 < q0 * low < v. Shifting both right by `s` bits that are 0 makes D1 shift them back.
// Here they are also above `j` random limbs of the dividend and `j` zero limbs of the divisor,
// and the divisor has zero limbs on top or none.
#[test]
fn div_rem_add_back() {
    let mut rng = Rng(3);
    let h = 1 << 63;
    for m in 3..=6 {
        for s in [0, 1, 32, 63] {
            for (w0, w1) in [(0, h), (u64::MAX, u64::MAX), (rng.next(), rng.next() | h)] {
                for q0 in [2, u64::MAX, rng.next() | 2] {
                    let mut v = rng.limbs(m - 2);
                    v[0] = ((rng.next() | h) >> s) << s;
                    v.extend([w0, w1]);
                    let mut u = vec![0; m + 1];
                    mul_into(&mut u[m - 2..], &[w0, w1], &[q0]);
                    for j in 0..=2 {
                        for high in 0..=1 {
                            let mut x = rng.limbs(j);
                            x.resize(j + m + 1, 0);
                            shr_into(&mut x[j..], &u, s);
                            let mut d = vec![0; j + m + high];
                            shr_into(&mut d[j..j + m], &v, s);
                            let q = check_div_rem(&mut rng, &x, &d);
                            assert_eq!(q, padded(&[q0 - 1], x.len()), "{:x?} / {:x?}", x, d);
                        }
                    }
                }
            }
        }
    }
}

// A divisor whose limbs are all 0 panics.
#[test]
#[should_panic(expected = "division by zero")]
fn div_rem_by_zero() {
    div_rem(&mut [0; 1], &mut [0; 2], &[1], &[0, 0], &mut [0; 5]);
}
