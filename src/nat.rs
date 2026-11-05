// A natural number of any size, for the bounds of interval literals in `src/parse.rs` and the
// digits of the bounds that `src/format.rs` prints.
//
// A `Nat` is its 64-bit limbs, the least significant first, with no zero limb at the top, so
// that 0 has no limbs and each number has exactly one representation. Products of limbs, with
// their carries, are computed in `u128`. `rocq/theories/Model.v` takes each operation below as
// the operation on `Z` that it computes, which is not proved, so each has to compute exactly
// that; `to_dec`, which only the layout of the printed text uses, is not modelled. The tests
// at the end compare them with `rug::Integer`.

use std::{
    cmp::Ordering,
    ops::{Add, Mul, Shl, Sub},
};

// With no zero limb at the top, the derived `PartialEq` compares values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Nat(Vec<u64>);

impl Nat {
    // The `Nat` of the limbs `v`, without the zero limbs at the top.
    fn from_limbs(mut v: Vec<u64>) -> Self {
        while v.last() == Some(&0) {
            v.pop();
        }
        Self(v)
    }

    /// `x` as a `Nat`.
    pub(crate) fn from_u64(x: u64) -> Self {
        Self::from_limbs(vec![x])
    }

    /// The number that the decimal digits `s` spell, which the grammar makes nonempty.
    pub(crate) fn from_dec(s: &str) -> Self {
        // 19 digits, below 10^19 < 2^64, at a time: n * 10^19 + the next 19. The first chunk
        // takes the digits left over, so that each of the others has 19.
        const CHUNK: usize = 19;
        let (head, tail) = s.as_bytes().split_at(s.len() % CHUNK);
        let mut n = Self(Vec::new());
        for c in std::iter::once(head).chain(tail.chunks(CHUNK)) {
            n.mul_add_u64(10u64.pow(c.len() as u32), digits(c, 10));
        }
        n
    }

    /// The number that the hexadecimal digits `s` spell, which the grammar makes nonempty.
    pub(crate) fn from_hex(s: &str) -> Self {
        // 16 digits make a limb, from the last digit up.
        Self::from_limbs(s.as_bytes().rchunks(16).map(|c| digits(c, 16)).collect())
    }

    /// `self == 0`.
    pub(crate) fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    /// The number of bits of `self`, which is 0 for 0: `2^(b - 1) <= self < 2^b` otherwise.
    pub(crate) fn bits(&self) -> u64 {
        match self.0.last() {
            None => 0,
            Some(top) => 64 * self.0.len() as u64 - u64::from(top.leading_zeros()),
        }
    }

    /// `self mod 2^128`.
    pub(crate) fn low_u128(&self) -> u128 {
        let limb = |i| u128::from(self.0.get(i).copied().unwrap_or(0));
        limb(0) | limb(1) << 64
    }

    /// `5^k`.
    pub(crate) fn pow5(k: u32) -> Self {
        // 5^k = 5^(k mod 27) * (5^27)^(k / 27), where 5^27 is the largest power of 5 below
        // 2^64: one multiplication by a limb at a time, in place, in a `Vec` that has room for
        // every limb of 5^k from the start. These are about k^2/1500 products of limbs, more
        // than the k^2/2300 of binary powering with schoolbook squares, but each costs less,
        // and no square needs a new `Vec`. On an x86-64 machine, this took less time for each
        // k from 27 to 10^6 that was timed: a sixth at k = 300 and 0.84 at k = 10^6. A
        // multiplication faster than schoolbook would change that for large k.
        const K: u32 = 27;
        let mut p = Self(Vec::with_capacity(pow5_limbs(k)));
        p.0.push(5u64.pow(k % K));
        for _ in 0..k / K {
            p.mul_add_u64(5u64.pow(K), 0);
        }
        p
    }

    /// `(self / d, self % d)`, the quotient rounded down. Panics if `d` is 0.
    pub(crate) fn div_rem(&self, d: &Nat) -> (Nat, Nat) {
        assert!(!d.is_zero(), "division by zero");
        if self < d {
            return (Self(Vec::new()), self.clone());
        }
        // For the `j` zero limbs at the bottom of `d`, d = d1 * B^j and self = s1 * B^j + s0
        // with B = 2^64 and s0 < B^j. Then self = (s1 / d1) * d + (s1 % d1) * B^j + s0, and
        // (s1 % d1) * B^j + s0 <= (d1 - 1) * B^j + B^j - 1 < d, so the quotient is s1 / d1
        // and the remainder (s1 % d1) * B^j + s0. A power of two, such as the divisor that
        // `scale` in `src/parse.rs` makes for `1e300`, thus takes a division by one limb. As
        // s0 < B^j, self >= d makes s1 > d1 - 1, so s1 >= d1.
        let j = d.0.iter().take_while(|&&x| x == 0).count();
        let (s0, s1) = self.0.split_at(j);
        let d1 = &d.0[j..];
        // The limbs of the remainder: those of s0, then those of s1 % d1 < d1.
        let mut r = Vec::with_capacity(d.0.len());
        r.extend_from_slice(s0);
        let q = if let [c] = *d1 {
            let (q, rc) = div_rem_u64(s1, c);
            r.push(rc);
            q
        } else {
            div_rem_knuth(s1, d1, &mut r)
        };
        (Self::from_limbs(q), Self::from_limbs(r))
    }

    /// The number of decimal digits of `self`, which is 0 for 0: `10^(d - 1) <= self < 10^d`
    /// otherwise.
    pub(crate) fn digits10(&self) -> u64 {
        let b = self.bits();
        if b == 0 {
            return 0;
        }
        // 1233/4096 < log10(2), so 10^d <= 2^(b - 1) <= self for this d: `self` has more than
        // d digits. As log10(2) - 1233/4096 < 5 * 10^-6, d falls short of the number of digits
        // less one by less than 1.31 + 5 * 10^-6 * b, so the loop raises it at most once for a
        // `self` of fewer than 10^5 bits.
        let mut d = u64::try_from(u128::from(b - 1) * 1233 / 4096).unwrap();
        while *self >= pow10(d + 1) {
            d += 1;
        }
        d + 1
    }

    /// The decimal digits of `self`, with no zero in front, and `"0"` for 0.
    pub(crate) fn to_dec(&self) -> String {
        // The remainders of repeated divisions by 10^19 < 2^64 are the chunks of 19 digits,
        // from the last one up. Only the top chunk is printed without its zeros in front.
        const CHUNK: u64 = 10u64.pow(19);
        let mut chunks = Vec::new();
        let mut x = self.clone();
        while !x.is_zero() {
            let (q, r) = div_rem_u64(&x.0, CHUNK);
            chunks.push(r);
            x = Self::from_limbs(q);
        }
        let mut s = match chunks.pop() {
            None => return String::from("0"),
            Some(top) => top.to_string(),
        };
        s.reserve(19 * chunks.len());
        for c in chunks.iter().rev() {
            s.push_str(&format!("{:019}", c));
        }
        s
    }

    // `self := self * m + a` for `m > 0`, which keeps the top limb nonzero.
    fn mul_add_u64(&mut self, m: u64, a: u64) {
        debug_assert!(m > 0);
        let mut carry = a;
        for x in &mut self.0 {
            // x * m + carry <= (2^64 - 1)^2 + 2^64 - 1 < 2^128.
            let t = u128::from(*x) * u128::from(m) + u128::from(carry);
            *x = t as u64;
            carry = (t >> 64) as u64;
        }
        if carry != 0 {
            self.0.push(carry);
        }
    }
}

// 10^k = 5^k * 2^k. Panics if k does not fit a `u32`.
fn pow10(k: u64) -> Nat {
    &Nat::pow5(u32::try_from(k).unwrap()) << k
}

// At least the number of limbs of 5^k: log2(5) < 149/64, so 5^k has at most
// floor(149k/64) + 1 bits, and so at most floor(149k/4096) + 1 limbs.
fn pow5_limbs(k: u32) -> usize {
    // 149k < 2^40 fits a `u64`, and the bound, below 2^28, a `usize`.
    usize::try_from(u64::from(k) * 149 / 4096 + 1).unwrap()
}

// The quotient `x / d` and the remainder `x % d` of the limbs `x` and a nonzero `d`, with the
// limbs of the quotient, the top ones of which may be 0.
fn div_rem_u64(x: &[u64], d: u64) -> (Vec<u64>, u64) {
    let d = u128::from(d);
    let mut q = vec![0; x.len()];
    let mut r = 0;
    // From the top limb down: `r < d`, so `(r * 2^64 + x) / d < 2^64`.
    for (q, &x) in q.iter_mut().zip(x).rev() {
        let t = r << 64 | u128::from(x);
        *q = (t / d) as u64;
        r = t % d;
    }
    (q, r as u64)
}

// The quotient `x / d` of the limbs `x` and `d`, for `x >= d`, a `d` of at least 2 limbs and
// no zero limb at the top of either, by Algorithm D of Knuth, The Art of Computer
// Programming, vol. 2, 3rd ed., 4.3.1, with base B = 2^64. It returns the limbs of the
// quotient, the top ones of which may be 0, and pushes those of the remainder `x % d` onto `r`,
// as many as `d` has. The comments name its steps.
fn div_rem_knuth(x: &[u64], d: &[u64], r: &mut Vec<u64>) -> Vec<u64> {
    const B: u128 = 1 << 64;
    let n = d.len();
    let m = x.len() - n;
    // D1: shift both by `s` bits so that the top limb of the divisor `v` is at least B/2,
    // which keeps each estimate of a quotient limb at most 2 too large (Theorem B). The
    // dividend `u` gets a limb more, which may be 0.
    let s = d[n - 1].leading_zeros();
    let mut v = Vec::with_capacity(n + 1);
    push_shl_bits(&mut v, d, s);
    v.pop();
    let mut u = Vec::with_capacity(x.len() + 1);
    push_shl_bits(&mut u, x, s);
    let (v1, v2) = (u128::from(v[n - 1]), u128::from(v[n - 2]));
    let mut q = vec![0; m + 1];
    // D2, D7: the limbs of the quotient from the top down. Before each step,
    // u[j..=j + n] < B * v, so that the quotient limb q[j] is below B.
    for j in (0..=m).rev() {
        // D3: estimate q[j] from the top two limbs of u[j..=j + n] and the top limb of
        // `v`, capped at B - 1, which gives a `qhat` with `qhat - 2 <= q[j] <= qhat`
        // (Theorems A and B), and `rhat = top - qhat * v1`. While `qhat` times the top two
        // limbs of `v` exceeds the top three limbs of u[j..=j + n], `qhat` is too large:
        // lower it. That cannot hold once `rhat >= B`, and it leaves `qhat` at `q[j]` or
        // `q[j] + 1`. The test computes `rhat * B` only for `rhat < B`, and the products
        // of `qhat < B`, so each fits a `u128`.
        let top = u128::from(u[j + n]) << 64 | u128::from(u[j + n - 1]);
        let mut qhat = (top / v1).min(B - 1);
        let mut rhat = top - qhat * v1;
        while rhat < B && qhat * v2 > (rhat << 64 | u128::from(u[j + n - 2])) {
            qhat -= 1;
            rhat += v1;
        }
        // D4: u[j..=j + n] -= qhat * v.
        let mut mul_carry = 0;
        let mut borrow = false;
        for (x, &y) in u[j..j + n].iter_mut().zip(&v) {
            // qhat * y + mul_carry <= (B - 1)^2 + B - 1 < B^2.
            let p = qhat * u128::from(y) + mul_carry;
            mul_carry = p >> 64;
            let (t, b1) = x.overflowing_sub(p as u64);
            let (t, b2) = t.overflowing_sub(u64::from(borrow));
            *x = t;
            borrow = b1 | b2;
        }
        let (t, b1) = u[j + n].overflowing_sub(mul_carry as u64);
        let (t, b2) = t.overflowing_sub(u64::from(borrow));
        u[j + n] = t;
        // D5, D6: if that went below 0, `qhat` was `q[j] + 1`: add `v` back once. This
        // happens with a probability of about 2/B, so the tests make it happen.
        if b1 | b2 {
            qhat -= 1;
            let mut carry = false;
            for (x, &y) in u[j..j + n].iter_mut().zip(&v) {
                let (t, c1) = x.overflowing_add(y);
                let (t, c2) = t.overflowing_add(u64::from(carry));
                *x = t;
                carry = c1 | c2;
            }
            // The carry out of the top limb cancels the borrow of D4.
            u[j + n] = u[j + n].wrapping_add(u64::from(carry));
        }
        q[j] = qhat as u64;
    }
    // D8: the remainder is u[..n], shifted back by `s` bits. It is below `v`, so u[n] is 0.
    r.extend((0..n).map(|i| ((u128::from(u[i + 1]) << 64 | u128::from(u[i])) >> s) as u64));
    q
}

// The value of the ASCII digits `s` in base `radix`, which has to fit a `u64`. Panics on a
// byte that is not a digit.
fn digits(s: &[u8], radix: u32) -> u64 {
    s.iter().fold(0, |n, &c| {
        n * u64::from(radix) + u64::from(char::from(c).to_digit(radix).unwrap())
    })
}

// Pushes onto `out` the limbs `x` shifted left by `s < 64` bits, with a limb more for the bits
// that leave the top, which may be 0.
fn push_shl_bits(out: &mut Vec<u64>, x: &[u64], s: u32) {
    let mut carry = 0;
    for &a in x {
        let t = u128::from(a) << s;
        out.push(t as u64 | carry);
        carry = (t >> 64) as u64;
    }
    out.push(carry);
}

impl Ord for Nat {
    fn cmp(&self, other: &Self) -> Ordering {
        // With no zero limb at the top, more limbs make a larger number, and between as many,
        // the top limb that differs decides. The derived `Ord` of `Vec` would compare the
        // lowest limbs first.
        self.0
            .len()
            .cmp(&other.0.len())
            .then_with(|| self.0.iter().rev().cmp(other.0.iter().rev()))
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Add<&Nat> for &Nat {
    type Output = Nat;

    fn add(self, rhs: &Nat) -> Nat {
        let (a, b) = if self.0.len() >= rhs.0.len() {
            (&self.0, &rhs.0)
        } else {
            (&rhs.0, &self.0)
        };
        let mut out = Vec::with_capacity(a.len() + 1);
        let mut carry = false;
        for (i, &x) in a.iter().enumerate() {
            let (t, c1) = x.overflowing_add(b.get(i).copied().unwrap_or(0));
            let (t, c2) = t.overflowing_add(u64::from(carry));
            out.push(t);
            carry = c1 | c2;
        }
        out.push(u64::from(carry));
        Nat::from_limbs(out)
    }
}

/// `self - rhs`. Panics if `rhs > self`.
impl Sub<&Nat> for &Nat {
    type Output = Nat;

    fn sub(self, rhs: &Nat) -> Nat {
        assert!(self >= rhs, "subtraction below zero");
        let mut out = Vec::with_capacity(self.0.len());
        let mut borrow = false;
        for (i, &x) in self.0.iter().enumerate() {
            let (t, b1) = x.overflowing_sub(rhs.0.get(i).copied().unwrap_or(0));
            let (t, b2) = t.overflowing_sub(u64::from(borrow));
            out.push(t);
            borrow = b1 | b2;
        }
        Nat::from_limbs(out)
    }
}

impl Mul<&Nat> for &Nat {
    type Output = Nat;

    fn mul(self, rhs: &Nat) -> Nat {
        // Schoolbook: out[i..] += x * rhs for each limb x = self[i].
        let mut out = vec![0; self.0.len() + rhs.0.len()];
        for (i, &x) in self.0.iter().enumerate() {
            let mut carry = 0;
            for (o, &y) in out[i..].iter_mut().zip(&rhs.0) {
                // x * y + o + carry <= (2^64 - 1)^2 + 2 * (2^64 - 1) = 2^128 - 1.
                let t = u128::from(x) * u128::from(y) + u128::from(*o) + carry;
                *o = t as u64;
                carry = t >> 64;
            }
            out[i + rhs.0.len()] = carry as u64;
        }
        Nat::from_limbs(out)
    }
}

/// `self * 2^rhs`.
impl Shl<u64> for &Nat {
    type Output = Nat;

    fn shl(self, rhs: u64) -> Nat {
        if self.is_zero() {
            return Nat(Vec::new());
        }
        // `rhs / 64` zero limbs, then the limbs shifted by the remaining bits, in one `Vec`.
        let j = usize::try_from(rhs / 64).unwrap();
        let mut out = Vec::with_capacity(j + self.0.len() + 1);
        out.resize(j, 0);
        push_shl_bits(&mut out, &self.0, (rhs % 64) as u32);
        Nat::from_limbs(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rug::{integer::Order, Integer};

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

        // A limb that is often 0, 1, 2^63 or all ones, to make carries and borrows run
        // across limbs.
        fn limb(&mut self) -> u64 {
            match self.below(8) {
                0 => 0,
                1 => 1,
                2 => 1 << 63,
                3 | 4 => u64::MAX,
                _ => self.next(),
            }
        }

        // A `Nat` of up to `max` limbs, whose top limb is often 1.
        fn nat(&mut self, max: u64) -> Nat {
            let len = self.below(max + 1) as usize;
            let mut v: Vec<u64> = (0..len).map(|_| self.limb()).collect();
            if len > 0 && self.below(4) == 0 {
                v[len - 1] = 1;
            }
            Nat::from_limbs(v)
        }
    }

    // The number of random cases, which can be set with `INARI_PARSE_N`.
    fn n_cases() -> u64 {
        std::env::var("INARI_PARSE_N")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(if cfg!(debug_assertions) {
                1_000
            } else {
                10_000
            })
    }

    // The random numbers of the test numbered `test`, which the seed `INARI_PARSE_SEED`
    // changes. Without it, they are those of `Rng(test)`.
    fn rng(test: u64) -> Rng {
        let seed = std::env::var("INARI_PARSE_SEED")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0);
        Rng(seed.wrapping_add(test))
    }

    fn int(x: &Nat) -> Integer {
        Integer::from_digits(&x.0, Order::Lsf)
    }

    fn nat(x: &Integer) -> Nat {
        assert!(*x >= 0);
        let mut v = vec![0; x.significant_digits::<u64>()];
        x.write_digits(&mut v, Order::Lsf);
        Nat::from_limbs(v)
    }

    // `x` has no zero limb at the top and is `y`.
    fn check(x: &Nat, y: &Integer) {
        assert_ne!(x.0.last(), Some(&0), "not normalized: {:?}", x);
        assert_eq!(int(x), *y);
    }

    // `to_dec` of `x` is the decimal digits that `rug` prints, and `digits10` is their number,
    // or 0 for 0.
    fn check_dec(x: &Nat) {
        let s = int(x).to_string();
        assert_eq!(x.to_dec(), s);
        let d = if x.is_zero() { 0 } else { s.len() as u64 };
        assert_eq!(x.digits10(), d, "{}", s);
    }

    // Each operation of `x` and `y`, and of `x` and the shifts in `shifts`, against `rug`.
    fn check_ops(x: &Nat, y: &Nat, shifts: &[u64]) {
        let (a, b) = (int(x), int(y));
        check(&(x + y), &Integer::from(&a + &b));
        check(&(x * y), &Integer::from(&a * &b));
        assert_eq!(x.cmp(y), a.cmp(&b), "{:?} {:?}", x, y);
        assert_eq!(x == y, a == b);
        if a >= b {
            check(&(x - y), &Integer::from(&a - &b));
        }
        if b != 0 {
            let (q, r) = x.div_rem(y);
            let (qq, rr) = a.clone().div_rem_floor(b.clone());
            check(&q, &qq);
            check(&r, &rr);
            // The quotient and the remainder of a product plus a remainder.
            let p = &(x * y) + &r;
            let (q, r2) = p.div_rem(y);
            check(&q, &a);
            check(&r2, &rr);
        }
        assert_eq!(x.bits(), u64::from(a.significant_bits()));
        assert_eq!(x.low_u128(), a.to_u128_wrapping());
        assert_eq!(x.is_zero(), a == 0);
        for &s in shifts {
            check(&(x << s), &Integer::from(&a << u32::try_from(s).unwrap()));
        }
    }

    // Numbers whose limbs carry and borrow at every step, or have their top limb 1, and the
    // single limbs.
    fn patterns() -> Vec<Nat> {
        let m = u64::MAX;
        let h = 1 << 63;
        let mut v = vec![
            vec![],
            vec![1],
            vec![2],
            vec![h],
            vec![m],
            vec![m - 1],
            vec![0, 1],
            vec![1, 1],
            vec![m, 1],
            vec![0, h],
            vec![m, h],
            vec![1, 2],
            vec![2, 1],
            vec![0, 0, 1],
            vec![m, m, 1],
            vec![1, 0, 0, 1],
            vec![m, 0, m],
            vec![0, m, 0, h],
            vec![5, 0, 0, h],
            vec![m - 1, m, m, m],
        ];
        for k in 1..=6 {
            v.push(vec![m; k]);
            let mut w = vec![0; k];
            w.push(1);
            v.push(w);
        }
        v.into_iter().map(Nat::from_limbs).collect()
    }

    #[test]
    fn small() {
        check(&Nat::from_u64(0), &Integer::new());
        assert!(Nat::from_u64(0).is_zero());
        for x in [1, 2, 10, 1 << 63, u64::MAX] {
            check(&Nat::from_u64(x), &Integer::from(x));
        }
    }

    #[test]
    fn ops_on_patterns() {
        let shifts = [0, 1, 63, 64, 65, 127, 128, 129, 1000, 100_000];
        let p = patterns();
        for x in &p {
            for y in &p {
                check_ops(x, y, &shifts);
            }
        }
    }

    #[test]
    fn zero_operands() {
        let zero = Nat::from_u64(0);
        let x = Nat::from_limbs(vec![3, 0, 7]);
        check(&(&zero + &zero), &Integer::new());
        check(&(&zero - &zero), &Integer::new());
        check(&(&x - &zero), &int(&x));
        check(&(&x - &x), &Integer::new());
        check(&(&zero * &x), &Integer::new());
        check(&(&x * &zero), &Integer::new());
        let (q, r) = zero.div_rem(&x);
        check(&q, &Integer::new());
        check(&r, &Integer::new());
        // No limbs are made for 0, however far it is shifted.
        check(&(&zero << u64::MAX), &Integer::new());
        assert_eq!(zero.bits(), 0);
        assert_eq!(zero.low_u128(), 0);
    }

    #[test]
    #[should_panic]
    fn div_by_zero() {
        Nat::from_u64(1).div_rem(&Nat::from_u64(0));
    }

    #[test]
    #[should_panic]
    fn sub_below_zero() {
        let _ = &Nat::from_limbs(vec![0, 1]) - &Nat::from_limbs(vec![1, 1]);
    }

    #[test]
    fn ord_by_value() {
        // The derived `Ord` of the limbs would say `[1, 2] < [2, 1]`.
        let x = Nat::from_limbs(vec![1, 2]);
        let y = Nat::from_limbs(vec![2, 1]);
        assert!(x > y);
        assert!(Nat::from_limbs(vec![0, 1]) > Nat::from_u64(u64::MAX));
        assert_eq!(x.cmp(&x.clone()), Ordering::Equal);
    }

    #[test]
    fn bits_of_powers_of_two() {
        let one = Nat::from_u64(1);
        for k in 0..300 {
            let p = &one << k;
            assert_eq!(p.bits(), k + 1);
            assert_eq!((&p - &one).bits(), k);
            check(&p, &(Integer::from(1) << k as u32));
        }
    }

    #[test]
    fn low_u128() {
        for (v, x) in [
            (vec![], 0),
            (vec![7], 7),
            (vec![1, 2], 2 << 64 | 1),
            (vec![u64::MAX, u64::MAX, 3], u128::MAX),
        ] {
            assert_eq!(Nat::from_limbs(v).low_u128(), x);
        }
    }

    #[test]
    fn pow5() {
        // Each `k` around a multiple of 27 up to 5400, where `pow5` takes one more factor
        // 5^27, and some above.
        let around_27 = (1..=200).flat_map(|m| [27 * m - 1, 27 * m, 27 * m + 1]);
        for k in (0..=300).chain(around_27).chain([12_345, 100_000]) {
            let p = Nat::pow5(k);
            check(&p, &Integer::from(Integer::u_pow_u(5, k)));
            // The `Vec` had room for every limb from the start.
            assert!(p.0.len() <= pow5_limbs(k), "{}", k);
        }
    }

    // The decimal and hexadecimal digits of `x`, after `zeros` zeros.
    fn digit_strings(x: &Integer, zeros: usize) -> [String; 2] {
        let z = "0".repeat(zeros);
        // The tests also take the hexadecimal digits in lower case, as the grammar takes both.
        [format!("{}{}", z, x), format!("{}{:X}", z, x)]
    }

    #[test]
    fn from_digits() {
        let ten = |k| Integer::from(Integer::u_pow_u(10, k));
        let mut cases = vec![
            Integer::new(),
            Integer::from(u64::MAX),
            Integer::from(u64::MAX) + 1,
            ten(19),
            ten(19) - 1,
            ten(38) - 1,
            ten(1000),
            Integer::from(Integer::u_pow_u(16, 64)) - 1,
        ];
        let mut rng = rng(1);
        for len in 1..200 {
            cases.push(int(&Nat::from_limbs(
                (0..len).map(|_| rng.limb()).collect(),
            )));
        }
        for x in &cases {
            for zeros in [0, 1, 18, 19, 20, 100] {
                let [dec, hex] = digit_strings(x, zeros);
                check(&Nat::from_dec(&dec), x);
                check(&Nat::from_hex(&hex), x);
                check(&Nat::from_hex(&hex.to_lowercase()), x);
            }
        }
        check(&Nat::from_dec(&"0".repeat(1000)), &Integer::new());
        check(&Nat::from_hex(&"0".repeat(1000)), &Integer::new());
        check(&Nat::from_hex("fF"), &Integer::from(255));
    }

    #[test]
    fn dec_of_patterns() {
        let t = 10u64.pow(19);
        for x in [0, 1, 9, 10, t / 10, t - 1, t, t + 1, u64::MAX] {
            check_dec(&Nat::from_u64(x));
        }
        // The patterns and their products, which have runs of all-ones limbs.
        let p = patterns();
        for x in &p {
            check_dec(x);
            for y in &p {
                check_dec(&(x * y));
            }
        }
    }

    // 10^k - 1, 10^k and 10^k + 1 for each k up to 1100. Where the number of digits passes a
    // multiple of 19 (k = 18, 19, 20, 38, 39, 57, ...), `to_dec` takes one more chunk of 19
    // digits, and its last chunks are all 9 or all 0.
    #[test]
    fn dec_around_powers_of_ten() {
        let one = Nat::from_u64(1);
        for k in 0..=1100u32 {
            let p = pow10(u64::from(k));
            check(&p, &Integer::from(Integer::u_pow_u(10, k)));
            check_dec(&(&p - &one));
            check_dec(&p);
            check_dec(&(&p + &one));
        }
    }

    // 2^k - 1, 2^k and 2^k + 1. Of the numbers of k + 1 bits, 2^k is the smallest, where the
    // estimate of `digits10` from the bits has the least room below the number of digits, and
    // 2^(k + 1) - 1 the largest, where its loop raises the estimate the most. The last two `k`
    // make numbers on both sides of the 10^5 bits up to which `digits10` says that its loop
    // raises the estimate at most once.
    #[test]
    fn dec_around_powers_of_two() {
        let one = Nat::from_u64(1);
        for k in (0..=2100).chain([4095, 4096, 4097, 99_999, 100_000]) {
            let p = &one << k;
            check_dec(&(&p - &one));
            check_dec(&p);
            check_dec(&(&p + &one));
        }
    }

    // c * 10^(19j) + r, whose chunks of 19 digits between the top and the last are all 0, and
    // 10^(19j) + 10^(19i) for i < j, a 1 at the end of a chunk among chunks of zeros. `to_dec`
    // prints each chunk of zeros as 19 zeros.
    #[test]
    fn dec_zero_chunks() {
        let t = 10u64.pow(19);
        let p: Vec<Nat> = (0..=60).map(|j| pow10(19 * j)).collect();
        for (j, pj) in p.iter().enumerate() {
            for c in [1, 7, t / 10, t - 1, t, u64::MAX] {
                let top = pj * &Nat::from_u64(c);
                for r in [0, 1, t / 10, t - 1] {
                    check_dec(&(&top + &Nat::from_u64(r)));
                }
            }
            for pi in &p[..j] {
                check_dec(&(pj + pi));
            }
        }
    }

    // Up to about 1200 decimal digits in runs of zeros, nines and random digits, so that whole
    // chunks of 19 digits are often all 0 or all 9, read by `from_dec` and printed back by
    // `to_dec`.
    #[test]
    fn dec_random_digit_runs() {
        let n = n_cases();
        let mut rng = rng(5);
        for _ in 0..n {
            let len = 1 + rng.below(1200) as usize;
            let mut s = String::with_capacity(len + 40);
            while s.len() < len {
                let kind = rng.below(3);
                for _ in 0..1 + rng.below(40) {
                    s.push(match kind {
                        0 => '0',
                        1 => '9',
                        _ => char::from(b'0' + rng.below(10) as u8),
                    });
                }
            }
            let x = Nat::from_dec(&s);
            check_dec(&x);
            let digits = s.trim_start_matches('0');
            assert_eq!(x.to_dec(), if digits.is_empty() { "0" } else { digits });
        }
        eprintln!("nat dec digit runs: {} cases", n);
    }

    // Divisions in which the estimate of a quotient limb after D3 is 1 too large, so that D6
    // adds the divisor back: for `v = w * B^(n - 2) + low` with `w` of 2 limbs, its top limb
    // at least B/2, and `0 < low < B^(n - 2)`, and a `u = q0 * w * B^(n - 2)` with
    // `1 < q0 < B`, D3 estimates `q0` from the top three limbs of `u` and the top two of `v`,
    // but `u / v = q0 - q0 * low / v`, and `0 < q0 * low < v`, so the quotient is `q0 - 1`.
    // For `q0 = 1`, also tested, `u < v`, which `div_rem` answers before Algorithm D.
    // Shifting both right by `s` bits that are 0 makes D1 shift them back. The same divisions
    // above `j` zero limbs, u * B^j + s0 by v * B^j for s0 < B^j, which `div_rem` strips from
    // the divisor, add back too, and have the remainder r * B^j + s0.
    #[test]
    fn div_rem_add_back() {
        let mut rng = rng(2);
        let h = 1 << 63;
        for n in 3..=6 {
            for s in [0, 1, 32, 63] {
                for (w0, w1) in [(0, h), (u64::MAX, u64::MAX), (rng.next(), rng.next() | h)] {
                    for q0 in [1, 2, u64::MAX, rng.next() | 1] {
                        let mut low: Vec<u64> = (0..n - 2).map(|_| rng.limb()).collect();
                        low[0] = ((rng.next() | h) >> s) << s;
                        let mut v = low;
                        v.extend([w0, w1]);
                        let mut w = vec![0; n - 2];
                        w.extend([w0, w1]);
                        let v = int(&Nat::from_limbs(v)) >> s;
                        let u = (int(&Nat::from_limbs(w)) * q0) >> s;
                        let (q, r) = nat(&u).div_rem(&nat(&v));
                        let (qq, rr) = u.clone().div_rem_floor(v.clone());
                        assert_eq!(qq, q0 - 1);
                        check(&q, &qq);
                        check(&r, &rr);
                        for j in [1, 2] {
                            let s0 = int(&Nat::from_limbs((0..j).map(|_| rng.limb()).collect()));
                            let b = 64 * j as u32;
                            let x = nat(&(Integer::from(&u << b) + &s0));
                            let (q, r) = x.div_rem(&nat(&Integer::from(&v << b)));
                            check(&q, &qq);
                            check(&r, &(Integer::from(&rr << b) + &s0));
                        }
                    }
                }
            }
        }
    }

    // Divisors with 0 to 79 zero limbs at the bottom, which `div_rem` strips: c * 2^t for an
    // odd limb c and t = 64 * i + 0, 1, 62 or 63 for i from 0 to 79, so that 2^t, such as
    // `scale` in `src/parse.rs` divides by, has 1 to 80 limbs, with dividends around them, of
    // up to 3 limbs more, and with quotients of up to 4 limbs.
    #[test]
    fn div_rem_low_zero_limbs() {
        let mut rng = rng(4);
        for limbs in 1..=80u32 {
            for bit in [0, 1, 62, 63] {
                let t = 64 * (limbs - 1) + bit;
                for c in [1, 3, 1 << 63 | 1, u64::MAX, rng.next() | 1] {
                    let d = Integer::from(c) << t;
                    let mut xs = vec![
                        Integer::from(&d - 1u32),
                        d.clone(),
                        Integer::from(&d + 1u32),
                        Integer::from(&d << 64u32) - 1u32,
                    ];
                    for _ in 0..4 {
                        let q = int(&rng.nat(3));
                        let r = int(&rng.nat(u64::from(limbs) + 1)) % &d;
                        xs.push(q * &d + r);
                        xs.push(int(&rng.nat(u64::from(limbs) + 3)));
                    }
                    for x in &xs {
                        let (q, r) = nat(x).div_rem(&nat(&d));
                        let (qq, rr) = x.clone().div_rem_floor(d.clone());
                        check(&q, &qq);
                        check(&r, &rr);
                    }
                }
            }
        }
    }

    #[test]
    fn divisor_longer_than_dividend() {
        let x = Nat::from_limbs(vec![u64::MAX; 3]);
        let y = Nat::from_limbs(vec![0, 0, 0, 1]);
        let (q, r) = x.div_rem(&y);
        assert!(q.is_zero());
        assert_eq!(r, x);
    }

    #[test]
    fn random() {
        let n = n_cases();
        let mut rng = rng(3);
        for _ in 0..n {
            let x = rng.nat(80);
            let y = rng.nat(80);
            let s = [rng.below(200), rng.below(1 << 16)];
            check_ops(&x, &y, &s);
            let [dec, hex] = digit_strings(&int(&x), rng.below(40) as usize);
            check(&Nat::from_dec(&dec), &int(&x));
            check(&Nat::from_hex(&hex), &int(&x));
            check_dec(&x);
        }
        eprintln!("nat random: {} cases", n);
    }
}
