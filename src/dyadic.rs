// Dyadic numbers of a fixed precision, enclosures of real numbers by them, and Ziv's strategy
// for rounding a real number to an `f64` from enclosures of increasing precision: the
// multi-precision kernel that the elementary functions will be computed with, without GMP.
//
// A `Dyadic<N>` is `(-1)^neg * m * 2^exp` for a mantissa `m` of `N` 64-bit limbs, the least
// significant first, at the precision p = 64 N bits. It is normalized: 0 is `m = 0` with
// `neg = false` and `exp = 0`, and any other number has the top bit of `m` set, so that each
// number has exactly one representation and tiny numbers keep their relative precision. Each
// operation is correctly rounded at p bits, toward +∞ if `up` and toward -∞ otherwise, by
// `round`, from an exact window of limbs and a sticky bit. The limb loops are those of
// `src/limbs.rs`, on scratch limbs that `with_buf` provides. Each function, here and in
// `src/limbs.rs`, writes every limb of the scratch that it reads before it reads it, so the
// contents of the scratch never matter.
//
// An exponent that leaves the range of `i64` panics. The theorems of
// `rocq/theories/DyOps.v` show that the arithmetic operations do not panic for operands in
// their domain whose exponents are at most 2^61 in magnitude (`exp_small` in
// `rocq/theories/DyRound.v`).
//
// `rocq/theories/Model.v` transcribes each function of this file except `with_buf` and the
// tests, so it has to be updated along with them. `rocq/theories/DyRound.v`,
// `rocq/theories/DyConv.v`, `rocq/theories/DyIsqrt.v`, `rocq/theories/DyOps.v` and
// `rocq/theories/DyDriver.v` prove them correct, and `rocq/theories/DyGrow.v` bounds the
// exponents of the enclosures that they return. `ziv` does not panic at its cap of 64 limbs:
// where no rounding test passes, it returns the bound of the enclosure at 64 limbs on the side
// of the rounding, rounded outward. `DyDriver.v` shows that it returns the correct rounding
// where a test passes, from a `start` of at most 64 as every function of the kernel gives
// (`ziv_strict_correct` and `ziv_strict_ziv`), and a value on the side of the rounding
// wherever the evaluation does not panic (`ziv_side`). That the value at the cap is within one
// `f64` of the correct rounding is not proved.
//
// The constants ln 2, ln 10 and π are in `src/dyadic/consts.rs`, the exponentials and the
// hyperbolic functions computed with the kernel in `src/dyadic/exp.rs`, the logarithms and the
// inverse hyperbolic functions in `src/dyadic/log.rs`, the inverse trigonometric functions in
// `src/dyadic/atan.rs`, the trigonometric functions in `src/dyadic/trig.rs`, and the powers
// x^y and x^n in `src/dyadic/pow.rs`, which have their own headers.

use crate::{limbs, simd::round_up_exact};
use std::cmp::Ordering;

mod atan;
mod consts;
mod exp;
mod log;
mod pow;
#[cfg(test)]
mod tests;
mod trig;

/// `(-1)^neg * m * 2^exp`, normalized as the header says.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Dyadic<const N: usize> {
    neg: bool,
    exp: i64,
    m: [u64; N],
}

/// The real numbers `lo <= x <= hi`, for `lo <= hi`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Encl<const N: usize> {
    pub(crate) lo: Dyadic<N>,
    pub(crate) hi: Dyadic<N>,
}

// Calls `f` with a zeroed scratch of at least 12 N + 16 limbs: on the stack for the precisions
// up to 256 bits, which Ziv's strategy tries first, and on the heap above.
fn with_buf<const N: usize, R>(f: impl FnOnce(&mut [u64]) -> R) -> R {
    if N <= 4 {
        f(&mut [0; 64])
    } else {
        f(&mut vec![0; 12 * N + 16])
    }
}

// Whether `x mod 2^k != 0`: some bit of `x` below bit `k` is set.
fn low_bits_nonzero(x: &[u64], k: u64) -> bool {
    let j = usize::try_from(k / 64).unwrap_or(usize::MAX);
    let s = k % 64;
    x.iter().take(j).any(|&l| l != 0) || x.get(j).copied().unwrap_or(0) & ((1 << s) - 1) != 0
}

// The `Dyadic<N>` that `(-1)^neg * (x + t) * 2^e` rounds to toward +∞ if `up`, and toward -∞
// otherwise, where `0 < t < 1` if `sticky` and `t = 0` otherwise. If `sticky`, `x` has to be
// at least 2^(p - 1), so that `t` is below the last bit that the result keeps. Panics if the
// exponent of the result does not fit an `i64`.
fn round<const N: usize>(neg: bool, x: &[u64], e: i64, sticky: bool, up: bool) -> Dyadic<N> {
    let l = limbs::bit_len(x);
    if l == 0 {
        // x = 0, and so not `sticky`.
        return Dyadic::ZERO;
    }
    // The top p bits of `x`, from bit `sh` up, which may be below bit 0. `l` is at most
    // 64 x.len() and p = 64 N, so `sh` fits an `i64`.
    let p = 64 * N as u64;
    let sh = l as i64 - p as i64;
    let mut m = [0; N];
    if sh >= 0 {
        limbs::shr_into(&mut m, x, sh as u64);
    } else {
        limbs::shl_into(&mut m, x, sh.unsigned_abs());
    }
    let mut exp = e.checked_add(sh).expect("exponent overflow");
    // The magnitude was truncated to `m * 2^exp`. Rounding toward +∞ increases it for a positive
    // number when something was dropped, and rounding toward -∞ does so for a negative one.
    let dropped = sticky || (sh > 0 && low_bits_nonzero(x, sh as u64));
    if dropped && up != neg && limbs::add_assign(&mut m, &[1]) {
        // m was 2^p - 1, and the sum, 2^p, is 2^(p - 1) * 2^1.
        m[N - 1] = 1 << 63;
        exp = exp.checked_add(1).expect("exponent overflow");
    }
    Dyadic { neg, exp, m }
}

impl<const N: usize> Dyadic<N> {
    pub(crate) const ZERO: Self = Self {
        neg: false,
        exp: 0,
        m: [0; N],
    };

    /// The value of the finite `x`, which is exact, as p >= 64 > 53.
    pub(crate) fn from_f64(x: f64) -> Self {
        assert!(x.is_finite());
        let bits = x.to_bits();
        let neg = bits >> 63 != 0;
        let be = ((bits >> 52) & 0x7ff) as i64;
        let f = bits & ((1 << 52) - 1);
        // |x| = f * 2^-1074 for a subnormal number or a zero, and (2^52 + f) * 2^(be - 1075)
        // otherwise.
        let (m, e) = if be == 0 {
            (f, -1074)
        } else {
            (f | (1 << 52), be - 1075)
        };
        round(neg, &[m], e, false, false)
    }

    pub(crate) fn is_zero(&self) -> bool {
        // The top limb of a nonzero number is nonzero.
        self.m[N - 1] == 0
    }

    pub(crate) fn neg(&self) -> Self {
        if self.is_zero() {
            *self
        } else {
            Self {
                neg: !self.neg,
                ..*self
            }
        }
    }

    /// `self * 2^k`, which is exact. Panics if the exponent does not fit an `i64`.
    pub(crate) fn shl(&self, k: i64) -> Self {
        if self.is_zero() {
            *self
        } else {
            Self {
                exp: self.exp.checked_add(k).expect("exponent overflow"),
                ..*self
            }
        }
    }

    // `|self|.cmp(|other|)`.
    fn cmp_abs(&self, other: &Self) -> Ordering {
        // Normalized, a larger exponent makes a larger magnitude, unless one of them is 0.
        match (self.is_zero(), other.is_zero()) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => self
                .exp
                .cmp(&other.exp)
                .then_with(|| limbs::cmp(&self.m, &other.m)),
        }
    }

    /// `self + other`, rounded toward +∞ if `up` and toward -∞ otherwise.
    pub(crate) fn add(&self, other: &Self, up: bool) -> Self {
        // An exact result needs no rounding.
        if other.is_zero() {
            return *self;
        }
        if self.is_zero() {
            return *other;
        }
        let (x, y) = if self.cmp_abs(other) == Ordering::Less {
            (other, self)
        } else {
            (self, other)
        };
        // |x| >= |y| makes x.exp >= y.exp, so the difference is in [0, 2^64): it is
        // `wrapping_sub` read as unsigned.
        let d = x.exp.wrapping_sub(y.exp) as u64;
        let e = x.exp.checked_sub(64).expect("exponent overflow");
        with_buf::<N, _>(|buf| {
            let (w, rest) = buf.split_at_mut(N + 2);
            let wy = &mut rest[..N + 1];
            // The window w = x.m * 2^64, in units of 2^(x.exp - 64), with a limb above for the
            // carry of a sum. In those units, |y| is y.m * 2^(64 - d): exact if d <= 64, and
            // otherwise wy + t, where 0 <= t < 1 and t > 0 exactly when bits of y.m below bit
            // d - 64 are set.
            w[0] = 0;
            w[1..=N].copy_from_slice(&x.m);
            w[N + 1] = 0;
            let sticky = if d <= 64 {
                limbs::shl_into(wy, &y.m, 64 - d);
                false
            } else {
                limbs::shr_into(wy, &y.m, d - 64);
                low_bits_nonzero(&y.m, d - 64)
            };
            if x.neg == y.neg {
                // w + wy < 2^(p + 65), so there is no carry out of w.
                limbs::add_assign(w, wy);
            } else {
                // w - (wy + t) = (w - wy - 1) + (1 - t) with 0 < 1 - t < 1 if t > 0, so that
                // `sticky` stays the sticky bit of the difference. If t > 0, then d > 64 and
                // wy < 2^(p - 1), so w - wy - 1 >= 2^(p - 1) as `round` asks.
                limbs::sub_assign(w, wy, sticky);
            }
            round(x.neg, w, e, sticky, up)
        })
    }

    /// `self - other`, rounded toward +∞ if `up` and toward -∞ otherwise.
    pub(crate) fn sub(&self, other: &Self, up: bool) -> Self {
        self.add(&other.neg(), up)
    }

    /// `self * other`, rounded toward +∞ if `up` and toward -∞ otherwise.
    pub(crate) fn mul(&self, other: &Self, up: bool) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::ZERO;
        }
        let e = self.exp.checked_add(other.exp).expect("exponent overflow");
        with_buf::<N, _>(|buf| {
            // The product of the mantissas is exact in 2N limbs.
            let w = &mut buf[..2 * N];
            limbs::mul_into(w, &self.m, &other.m);
            round(self.neg != other.neg, w, e, false, up)
        })
    }

    /// `self * k`, rounded toward +∞ if `up` and toward -∞ otherwise.
    pub(crate) fn mul_u64(&self, k: u64, up: bool) -> Self {
        if self.is_zero() || k == 0 {
            return Self::ZERO;
        }
        with_buf::<N, _>(|buf| {
            // m * k is exact in N + 1 limbs.
            let w = &mut buf[..N + 1];
            w[..N].copy_from_slice(&self.m);
            w[N] = limbs::mul_add_limb(&mut w[..N], k, 0);
            round(self.neg, w, self.exp, false, up)
        })
    }

    /// `self / k`, rounded toward +∞ if `up` and toward -∞ otherwise. Panics if `k` is 0.
    pub(crate) fn div_u64(&self, k: u64, up: bool) -> Self {
        assert!(k != 0, "division by zero");
        if self.is_zero() {
            return Self::ZERO;
        }
        let e = self.exp.checked_sub(64).expect("exponent overflow");
        with_buf::<N, _>(|buf| {
            // |self| = (m * 2^64) * 2^(exp - 64) = (q + r / k) * k * 2^(exp - 64). As k < 2^64,
            // q >= 2^(p - 1), as `round` asks of a sticky quotient.
            let (x, q) = buf.split_at_mut(N + 1);
            let q = &mut q[..N + 1];
            x[0] = 0;
            x[1..].copy_from_slice(&self.m);
            let r = limbs::div_rem_limb(q, x, k);
            round(self.neg, q, e, r != 0, up)
        })
    }

    /// `self / other`, rounded toward +∞ if `up` and toward -∞ otherwise. Panics if `other`
    /// is 0.
    pub(crate) fn div(&self, other: &Self, up: bool) -> Self {
        assert!(!other.is_zero(), "division by zero");
        if self.is_zero() {
            return Self::ZERO;
        }
        let e = self
            .exp
            .checked_sub(other.exp)
            .and_then(|e| e.checked_sub(64 * N as i64))
            .expect("exponent overflow");
        with_buf::<N, _>(|buf| {
            // |self / other| = (q + r / other.m) * 2^(self.exp - other.exp - p) for the
            // quotient q and remainder r of self.m * 2^p by other.m. As
            // 2^(p - 1) <= self.m, other.m < 2^p, q >= 2^(p - 1), as `round` asks of a sticky
            // quotient.
            let (x, rest) = buf.split_at_mut(2 * N);
            let (q, rest) = rest.split_at_mut(2 * N);
            let (r, scratch) = rest.split_at_mut(N);
            x[..N].fill(0);
            x[N..].copy_from_slice(&self.m);
            limbs::div_rem(q, r, x, &other.m, scratch);
            let sticky = r.iter().any(|&l| l != 0);
            round(self.neg != other.neg, q, e, sticky, up)
        })
    }

    /// The square root of `self`, rounded toward +∞ if `up` and toward -∞ otherwise. Panics if
    /// `self` is negative.
    pub(crate) fn sqrt(&self, up: bool) -> Self {
        if self.is_zero() {
            return Self::ZERO;
        }
        assert!(!self.neg, "square root of a negative number");
        // self = X * 2^(2 e) for X = m * 2^(p + δ), where δ in {0, 1} makes exp - δ even, and
        // e = (exp - δ) / 2 - p / 2. The square root is (s + t) * 2^e for s = isqrt(X), with
        // 0 < t < 1 exactly when s^2 != X. As 2^(2p - 1) <= X, s >= 2^(p - 1), as `round` asks.
        let delta = self.exp.rem_euclid(2) as u64;
        let e = self.exp.div_euclid(2) - 32 * N as i64;
        with_buf::<N, _>(|buf| {
            let (x, rest) = buf.split_at_mut(2 * N + 1);
            let (s, rest) = rest.split_at_mut(N + 1);
            limbs::shl_into(x, &self.m, 64 * N as u64 + delta);
            isqrt(s, x, rest);
            let sq = &mut rest[..2 * N + 2];
            limbs::mul_into(sq, s, s);
            let sticky = limbs::cmp(sq, x) != Ordering::Equal;
            round(false, s, e, sticky, up)
        })
    }

    /// `self` rounded toward +∞ if `up` and toward -∞ otherwise to an `f64`. A zero gives +0.
    pub(crate) fn to_f64(self, up: bool) -> f64 {
        if self.is_zero() {
            0.0
        } else if up {
            self.round_up(self.neg)
        } else {
            // Rounding toward -∞ is -round_up(-x).
            -self.round_up(!self.neg)
        }
    }

    // `(-1)^neg * |self|` rounded toward +∞ to an `f64`, for a nonzero `self`, as
    // `round_up_scaled` of `src/parse.rs` rounds the magnitude of a literal.
    fn round_up(&self, neg: bool) -> f64 {
        // 2^(b - 1) <= |self| < 2^b.
        let b = i128::from(self.exp) + 64 * N as i128;
        if b >= 1025 {
            // |self| >= 2^1024 > MAX.
            return if neg { f64::MIN } else { f64::INFINITY };
        }
        if b <= -1074 {
            // 0 < |self| < 2^-1074. A tiny negative number rounds to -0, as `round_up_exact`
            // rounds it.
            return if neg { -0.0 } else { f64::from_bits(1) };
        }
        // The top 128 bits of m, at 2^(b - 128), with the lower limbs as the sticky bit.
        // `round_up_exact` asks for 2^52 <= q if `sticky`, and |b - 128| <= 2^20.
        let lo = N.checked_sub(2).map_or(0, |i| self.m[i]);
        let q = u128::from(self.m[N - 1]) << 64 | u128::from(lo);
        let sticky = self.m[..N.saturating_sub(2)].iter().any(|&l| l != 0);
        round_up_exact(neg, q, (b - 128) as i32, sticky)
    }
}

// The order of the values, which agrees with the derived `PartialEq` of the representations, as
// each number has exactly one.
impl<const N: usize> Ord for Dyadic<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        let sign = |x: &Self| {
            if x.is_zero() {
                0
            } else if x.neg {
                -1
            } else {
                1
            }
        };
        match sign(self).cmp(&sign(other)) {
            Ordering::Equal if self.neg => other.cmp_abs(self),
            Ordering::Equal => self.cmp_abs(other),
            o => o,
        }
    }
}

impl<const N: usize> PartialOrd for Dyadic<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// `s := floor(sqrt(x))`, for `s.len() == n + 1`, `x.len() == 2 n + 1` and
// 2^(128 n - 1) <= x < 2^(128 n + 1) with n >= 1, and `scratch.len() >= 7 n + 7`.
fn isqrt(s: &mut [u64], x: &[u64], scratch: &mut [u64]) {
    let (y, rest) = scratch.split_at_mut(s.len());
    let (q, rest) = rest.split_at_mut(x.len());
    let (r, rest) = rest.split_at_mut(s.len());
    // The seed: c, the top 32 bits of the significand of sqrt(u), for u the top bits t = x >> 2k
    // of `x` with their low 11 bits cleared, so that 2^31 <= c < 2^32 and c * 2^k is near
    // sqrt(x). `x` has l = 128 n or 128 n + 1 bits, and 2k is l - 63 or l - 64, so
    // 2^62 <= t < 2^64 and 2^(64 n - 1) <= c * 2^k < 2^(64 n + 1). u has at most 53
    // significant bits, so `u as f64` is exact, and u <= 2^64 - 2^11, whose square root rounds
    // below 2^32. `t as f64` would round each t >= 2^64 - 2^10 up to 2^64, whose square root
    // 2^32 has no fraction bits, which would make c = 2^31 and c * 2^k near sqrt(x) / 2, from
    // which the iteration takes about 5 more steps. Only 2^31 <= c < 2^32 matters for the
    // result, which the bits of `c` ensure whatever `sqrt` returns: its 52 bits of fraction
    // under the implicit bit, shifted to 32 bits.
    let l = limbs::bit_len(x);
    let k = (l - 63) / 2;
    let mut t = [0];
    limbs::shr_into(&mut t, x, 2 * k);
    let u = t[0] & !((1 << 11) - 1);
    let c = (((u as f64).sqrt().to_bits() & ((1 << 52) - 1)) | 1 << 52) >> 21;
    limbs::shl_into(s, &[c], k);
    // Newton's iteration for floor(sqrt(x)) (Zimmermann, Karatsuba Square Root, INRIA RR-3805,
    // 1999, and Brent and Zimmermann, Modern Computer Arithmetic, 1.5.1):
    // y = floor((s + floor(x / s)) / 2). The first step makes y >= isqrt(x) from any s > 0 (by
    // the inequality of the arithmetic and geometric means), and each step after it lowers s
    // while s > isqrt(x). Once y >= s, s = isqrt(x). Every s and y is below 2^(64 s.len()).
    let mut first = true;
    loop {
        limbs::div_rem(q, r, x, s, rest);
        limbs::add_assign(q, s);
        limbs::shr_into(y, q, 1);
        if !first && limbs::cmp(y, s) != Ordering::Less {
            return;
        }
        first = false;
        s.copy_from_slice(y);
    }
}

impl<const N: usize> Encl<N> {
    /// The enclosure of the finite `x`, which is exact.
    pub(crate) fn point(x: f64) -> Self {
        let d = Dyadic::from_f64(x);
        Self { lo: d, hi: d }
    }

    pub(crate) fn neg(&self) -> Self {
        Self {
            lo: self.hi.neg(),
            hi: self.lo.neg(),
        }
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        Self {
            lo: self.lo.add(&other.lo, false),
            hi: self.hi.add(&other.hi, true),
        }
    }

    pub(crate) fn sub(&self, other: &Self) -> Self {
        Self {
            lo: self.lo.sub(&other.hi, false),
            hi: self.hi.sub(&other.lo, true),
        }
    }

    pub(crate) fn mul(&self, other: &Self) -> Self {
        let (a, b, c, d) = (&self.lo, &self.hi, &other.lo, &other.hi);
        if !a.neg && !c.neg {
            // Over enclosures of nonnegative numbers, x * y is least at the lower bounds and
            // greatest at the upper bounds. A zero has `neg == false`.
            return Self {
                lo: a.mul(c, false),
                hi: b.mul(d, true),
            };
        }
        // The extremes of x * y over the enclosures are among the products of their bounds.
        // Choosing the products by the signs of the bounds would save most of them in the
        // other cases too.
        Self {
            lo: a
                .mul(c, false)
                .min(a.mul(d, false))
                .min(b.mul(c, false))
                .min(b.mul(d, false)),
            hi: a
                .mul(c, true)
                .max(a.mul(d, true))
                .max(b.mul(c, true))
                .max(b.mul(d, true)),
        }
    }

    /// Panics if `other` contains 0.
    pub(crate) fn div(&self, other: &Self) -> Self {
        assert!(
            other.lo > Dyadic::ZERO || other.hi < Dyadic::ZERO,
            "division by an enclosure of zero"
        );
        let (a, b, c, d) = (&self.lo, &self.hi, &other.lo, &other.hi);
        if !c.neg {
            // Then c > 0, by the assertion and c <= d. For y > 0, x / y is least at x = a and
            // greatest at x = b. a / y is least at y = d if a >= 0 and at y = c if a < 0, and
            // b / y is greatest at y = c if b >= 0 and at y = d if b < 0. A zero has
            // `neg == false`.
            return Self {
                lo: a.div(if a.neg { c } else { d }, false),
                hi: b.div(if b.neg { d } else { c }, true),
            };
        }
        // Without 0 in the divisor, x / y is monotonic in each argument over the enclosures,
        // so its extremes are among the quotients of their bounds.
        Self {
            lo: a
                .div(c, false)
                .min(a.div(d, false))
                .min(b.div(c, false))
                .min(b.div(d, false)),
            hi: a
                .div(c, true)
                .max(a.div(d, true))
                .max(b.div(c, true))
                .max(b.div(d, true)),
        }
    }

    /// The square roots of the nonnegative numbers of `self`. Panics if `self.hi < 0`.
    pub(crate) fn sqrt(&self) -> Self {
        Self {
            lo: self.lo.max(Dyadic::ZERO).sqrt(false),
            hi: self.hi.sqrt(true),
        }
    }

    pub(crate) fn mul_u64(&self, k: u64) -> Self {
        Self {
            lo: self.lo.mul_u64(k, false),
            hi: self.hi.mul_u64(k, true),
        }
    }

    /// Panics if `k` is 0.
    pub(crate) fn div_u64(&self, k: u64) -> Self {
        Self {
            lo: self.lo.div_u64(k, false),
            hi: self.hi.div_u64(k, true),
        }
    }

    /// `self * 2^k`, which is exact.
    pub(crate) fn shl(&self, k: i64) -> Self {
        Self {
            lo: self.lo.shl(k),
            hi: self.hi.shl(k),
        }
    }
}

/// An enclosure of a real number at any precision, which Ziv's strategy refines.
pub(crate) trait Eval {
    fn eval<const N: usize>(&self) -> Encl<N>;
}

/// `round_bounds(f, up) = (lo, hi)`, the bounds of `f.eval::<N>()` rounded toward +∞ if `up`
/// and toward -∞ otherwise to `f64`s.
fn round_bounds<const N: usize, E: Eval>(f: &E, up: bool) -> (f64, f64) {
    let x = f.eval::<N>();
    (x.lo.to_f64(up), x.hi.to_f64(up))
}

/// Ziv's rounding test at `N` limbs: the number that `f` encloses rounded toward +∞ if `up`
/// and toward -∞ otherwise to an `f64`, if both bounds of `f.eval::<N>()` round to it.
/// Directed rounding is monotonic, so that number is then also the rounding of each number
/// between them.
pub(crate) fn ziv_at<const N: usize, E: Eval>(f: &E, up: bool) -> Option<f64> {
    let (lo, hi) = round_bounds::<N, E>(f, up);
    // `==` takes -0 and +0 as equal, either of which is a zero rounded as MPFR rounds it.
    if lo == hi {
        Some(lo)
    } else {
        None
    }
}

/// The last step of Ziv's strategy, at its cap of 64 limbs, that is, 4,096 bits: the rounding
/// test of `ziv_at`, and where it fails, the bound of `f.eval::<64>()` on the side of the
/// rounding, rounded outward: the upper bound rounded toward +∞ if `up`, and the lower bound
/// rounded toward -∞ otherwise. Either way the result is on that side of the number that `f`
/// encloses, but it is known to be its correct rounding only where the test passes.
fn ziv_cap<E: Eval>(f: &E, up: bool) -> f64 {
    let (lo, hi) = round_bounds::<64, E>(f, up);
    // The test passes where `lo == hi`, and then `lo` is returned as in `ziv_at`.
    if lo == hi || !up {
        lo
    } else {
        hi
    }
}

/// The number that `f` encloses rounded toward +∞ if `up` and toward -∞ otherwise to an `f64`,
/// by Ziv's strategy: the rounding test at each of 1, 2, 4, 8, 16 and 32 limbs that is at least
/// `start`, in that order, until it passes, and then `ziv_cap` at 64 limbs, whatever `start`
/// is. The result is correctly rounded if a test passes. Where none does, it is the outward
/// rounding of the enclosure at 64 limbs, which is on the correct side of the number but not
/// known to be its correct rounding.
pub(crate) fn ziv<E: Eval>(f: &E, up: bool, start: usize) -> f64 {
    macro_rules! try_levels {
        ($($n:literal),*) => {
            $(
                if start <= $n {
                    if let Some(x) = ziv_at::<$n, E>(f, up) {
                        return x;
                    }
                }
            )*
        };
    }
    try_levels!(1, 2, 4, 8, 16, 32);
    ziv_cap(f, up)
}
