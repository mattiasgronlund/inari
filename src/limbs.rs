// Loops on the 64-bit limbs of natural numbers, which `Nat` in `src/nat.rs` and the dyadic
// numbers of `src/dyadic.rs` share. A slice `x` of limbs, the least significant first, holds
// the number sum x[i] * 2^(64 i), and may have zero limbs at the top. Products of limbs, with
// their carries, are computed in `u128`. `rocq/theories/Model.v` transcribes each function
// below, so it has to be updated along with them, and `rocq/theories/Limbs.v`,
// `rocq/theories/KnuthStep.v` and `rocq/theories/Knuth.v` prove that each computes the
// operation on integers that its comment gives.

use std::cmp::Ordering;

#[cfg(test)]
mod tests;

/// The number of bits of `x`, which is 0 for 0: `2^(b - 1) <= x < 2^b` otherwise.
pub(crate) fn bit_len(x: &[u64]) -> u64 {
    match x.iter().rposition(|&l| l != 0) {
        None => 0,
        Some(i) => 64 * i as u64 + 64 - u64::from(x[i].leading_zeros()),
    }
}

/// `x.cmp(y)` of the numbers that `x` and `y` hold, whatever their lengths.
pub(crate) fn cmp(x: &[u64], y: &[u64]) -> Ordering {
    // From the top limb down, a limb past the end being 0: the first that differs decides.
    let limb = |x: &[u64], i: usize| x.get(i).copied().unwrap_or(0);
    for i in (0..x.len().max(y.len())).rev() {
        let (a, b) = (limb(x, i), limb(y, i));
        if a != b {
            return a.cmp(&b);
        }
    }
    Ordering::Equal
}

/// `x := (x + y) mod 2^(64 x.len())`, for a `y` no longer than `x`. Returns the carry out of the
/// top limb of `x`.
pub(crate) fn add_assign(x: &mut [u64], y: &[u64]) -> bool {
    let mut carry = false;
    for (i, a) in x.iter_mut().enumerate() {
        let (t, c1) = a.overflowing_add(y.get(i).copied().unwrap_or(0));
        let (t, c2) = t.overflowing_add(u64::from(carry));
        *a = t;
        carry = c1 | c2;
    }
    carry
}

/// `x := (x - y - borrow) mod 2^(64 x.len())`, for a `y` no longer than `x`. Returns the borrow
/// out of the top limb of `x`, which is set if and only if `x < y + borrow` before the call.
pub(crate) fn sub_assign(x: &mut [u64], y: &[u64], borrow: bool) -> bool {
    let mut borrow = borrow;
    for (i, a) in x.iter_mut().enumerate() {
        let (t, b1) = a.overflowing_sub(y.get(i).copied().unwrap_or(0));
        let (t, b2) = t.overflowing_sub(u64::from(borrow));
        *a = t;
        borrow = b1 | b2;
    }
    borrow
}

/// `x := (x * m + a) mod 2^(64 x.len())`. Returns the limb above the top one,
/// `(x * m + a) >> (64 x.len())`.
pub(crate) fn mul_add_limb(x: &mut [u64], m: u64, a: u64) -> u64 {
    let mut carry = a;
    for l in x.iter_mut() {
        // l * m + carry <= (2^64 - 1)^2 + 2^64 - 1 < 2^128.
        let t = u128::from(*l) * u128::from(m) + u128::from(carry);
        *l = t as u64;
        carry = (t >> 64) as u64;
    }
    carry
}

/// `out := x * y`, for `out.len() == x.len() + y.len()`, which holds every product.
pub(crate) fn mul_into(out: &mut [u64], x: &[u64], y: &[u64]) {
    // Schoolbook: out[i..=i + y.len()] += a * y for each limb a = x[i], where out[i + y.len()]
    // is still 0.
    out.fill(0);
    for (i, &a) in x.iter().enumerate() {
        let (row, top) = out[i..].split_at_mut(y.len());
        top[0] = mul_add_row(row, y, a);
    }
}

// `row := (row + a * y) mod 2^(64 y.len())`, for `row.len() == y.len()`. Returns the limb above
// the top one.
fn mul_add_row(row: &mut [u64], y: &[u64], a: u64) -> u64 {
    let mut carry = 0;
    for (o, &b) in row.iter_mut().zip(y) {
        // a * b + o + carry <= (2^64 - 1)^2 + 2 * (2^64 - 1) = 2^128 - 1.
        let t = u128::from(a) * u128::from(b) + u128::from(*o) + carry;
        *o = t as u64;
        carry = t >> 64;
    }
    carry as u64
}

/// `out := (x << sh) mod 2^(64 out.len())`.
pub(crate) fn shl_into(out: &mut [u64], x: &[u64], sh: u64) {
    // `sh / 64` zero limbs, then the limbs of `x` shifted by the remaining bits.
    let j = usize::try_from(sh / 64)
        .unwrap_or(usize::MAX)
        .min(out.len());
    let s = (sh % 64) as u32;
    let (zeros, out) = out.split_at_mut(j);
    // A fill of no limbs can still call `memset`, which costs more than the test.
    if j > 0 {
        zeros.fill(0);
    }
    let mut carry = 0;
    for (i, o) in out.iter_mut().enumerate() {
        let t = u128::from(x.get(i).copied().unwrap_or(0)) << s;
        *o = t as u64 | carry;
        carry = (t >> 64) as u64;
    }
}

/// `out := (x >> sh) mod 2^(64 out.len())`.
pub(crate) fn shr_into(out: &mut [u64], x: &[u64], sh: u64) {
    // The limbs of `x` from limb `sh / 64` up, each limb of `out` taking the 64 bits from bit
    // `sh % 64` of two of them.
    let j = usize::try_from(sh / 64).unwrap_or(usize::MAX);
    let x = x.get(j..).unwrap_or(&[]);
    let s = (sh % 64) as u32;
    let limb = |i: usize| u128::from(x.get(i).copied().unwrap_or(0));
    for (i, o) in out.iter_mut().enumerate() {
        *o = ((limb(i + 1) << 64 | limb(i)) >> s) as u64;
    }
}

/// `q := x / d` and returns `x % d`, for `q.len() == x.len()` and `d > 0`.
pub(crate) fn div_rem_limb(q: &mut [u64], x: &[u64], d: u64) -> u64 {
    let d = u128::from(d);
    let mut r = 0;
    // From the top limb down: `r < d`, so `(r * 2^64 + x) / d < 2^64`.
    for (q, &x) in q.iter_mut().zip(x).rev() {
        let t = r << 64 | u128::from(x);
        *q = (t / d) as u64;
        r = t % d;
    }
    r as u64
}

/// `q := x / d` and `r := x % d`, for `q.len() == x.len()`, `r.len() == d.len()` and
/// `scratch.len() >= x.len() + d.len() + 2`. Panics if `d` is 0.
pub(crate) fn div_rem(q: &mut [u64], r: &mut [u64], x: &[u64], d: &[u64], scratch: &mut [u64]) {
    let n = d.iter().rposition(|&l| l != 0).expect("division by zero") + 1;
    if cmp(x, d) == Ordering::Less {
        // x < d < 2^(64 n), so the limbs of `x` from `n` up are 0.
        q.fill(0);
        for (i, l) in r.iter_mut().enumerate() {
            *l = x.get(i).copied().unwrap_or(0);
        }
        return;
    }
    // For the `j` zero limbs at the bottom of `d`, d = d1 * B^j and x = s1 * B^j + s0 with
    // B = 2^64 and s0 < B^j. Then x = (s1 / d1) * d + (s1 % d1) * B^j + s0, and
    // (s1 % d1) * B^j + s0 <= (d1 - 1) * B^j + B^j - 1 < d, so the quotient is s1 / d1 and the
    // remainder (s1 % d1) * B^j + s0. A power of two, such as the divisor that `scale` in
    // `src/parse.rs` makes for `1e300`, thus takes a division by one limb. As s0 < B^j,
    // x >= d makes s1 > d1 - 1, so s1 >= d1, and `s1` has at least as many limbs as `d1`.
    let j = d.iter().take_while(|&&l| l == 0).count();
    let (s0, s1) = x.split_at(j);
    let d1 = &d[j..n];
    // The quotient s1 / d1 fits the k = s1.len() - d1.len() + 1 limbs q[..k], and the remainder
    // the n limbs r[..n], of which r[..j] is s0: each branch writes q[..k] and r[j..n], and the
    // limbs above them are 0. A fill or a copy of no limbs can still call `memset` or `memcpy`,
    // which costs more than the test.
    let k = s1.len() - d1.len() + 1;
    if j > 0 {
        r[..j].copy_from_slice(s0);
    }
    if let [c] = *d1 {
        r[j] = div_rem_limb(&mut q[..k], s1, c);
    } else {
        div_rem_knuth(&mut q[..k], &mut r[j..n], s1, d1, scratch);
    }
    if k < q.len() {
        q[k..].fill(0);
    }
    if n < r.len() {
        r[n..].fill(0);
    }
}

// `q := x / d` and `r := x % d`, for a `d` of at least 2 limbs with no zero limb at the top,
// `x.len() >= d.len()`, `q.len() == x.len() - d.len() + 1`, `r.len() == d.len()` and
// `scratch.len() >= x.len() + d.len() + 2`, by Algorithm D of Knuth, The Art of Computer
// Programming, vol. 2, 3rd ed., 4.3.1, with base B = 2^64. The comments name its steps.
fn div_rem_knuth(q: &mut [u64], r: &mut [u64], x: &[u64], d: &[u64], scratch: &mut [u64]) {
    let n = d.len();
    let m = x.len() - n;
    // D1: shift both by `s` bits so that the top limb of the divisor `v` is at least B/2,
    // which keeps each estimate of a quotient limb at most 2 too large (Theorem B). The
    // dividend `u` gets a limb more, which may be 0, and so does `v`, which is 0 and unused.
    let s = d[n - 1].leading_zeros();
    let (u, v) = scratch.split_at_mut(x.len() + 1);
    let v = &mut v[..n + 1];
    shl_into(v, d, u64::from(s));
    shl_into(u, x, u64::from(s));
    let v = &v[..n];
    // D2, D7: the limbs of the quotient from the top down. Step `j` works on the window
    // u[j..=j + n] and leaves u[j..j + n] for the next one. Before each step,
    // u[j + 1..=j + n] < v, so that the quotient limb q[j] is below B.
    for j in (0..=m).rev() {
        q[j] = knuth_step(&mut u[j..=j + n], v);
    }
    // D8: the remainder is u[..n], shifted back by `s` bits.
    shr_into(r, &u[..n], u64::from(s));
}

// D3-D6 of `div_rem_knuth` on a window `w` of `v.len() + 1` limbs with w[1..] < v, for a `v`
// of at least 2 limbs whose top limb is at least B/2, as D1 makes it: returns q = w / v, which
// is below B, and leaves w := w - q * v.
fn knuth_step(w: &mut [u64], v: &[u64]) -> u64 {
    const B: u128 = 1 << 64;
    let n = v.len();
    let (v1, v2) = (u128::from(v[n - 1]), u128::from(v[n - 2]));
    // D3: estimate q from the top two limbs of `w` and the top limb of `v`, capped at B - 1,
    // which gives a `qhat` with `qhat - 2 <= q <= qhat` (Theorems A and B), and
    // `rhat = top - qhat * v1`. While `qhat` times the top two limbs of `v` exceeds the top
    // three limbs of `w`, `qhat` is too large: lower it. That cannot hold once `rhat >= B`, and
    // it leaves `qhat` at `q` or `q + 1`. The test computes `rhat * B` only for `rhat < B`,
    // and the products of `qhat < B`, so each fits a `u128`.
    let top = u128::from(w[n]) << 64 | u128::from(w[n - 1]);
    let mut qhat = (top / v1).min(B - 1);
    let mut rhat = top - qhat * v1;
    while rhat < B && qhat * v2 > (rhat << 64 | u128::from(w[n - 2])) {
        qhat -= 1;
        rhat += v1;
    }
    // D4: w -= qhat * v.
    let mut mul_carry = 0;
    let mut borrow = false;
    for (x, &y) in w[..n].iter_mut().zip(v) {
        // qhat * y + mul_carry <= (B - 1)^2 + B - 1 < B^2.
        let p = qhat * u128::from(y) + mul_carry;
        mul_carry = p >> 64;
        let (t, b1) = x.overflowing_sub(p as u64);
        let (t, b2) = t.overflowing_sub(u64::from(borrow));
        *x = t;
        borrow = b1 | b2;
    }
    let (t, b1) = w[n].overflowing_sub(mul_carry as u64);
    let (t, b2) = t.overflowing_sub(u64::from(borrow));
    w[n] = t;
    // D5, D6: if that went below 0, `qhat` was `q + 1`: add `v` back once. This happens with a
    // probability of about 2/B, so the tests make it happen. The carry out of the top limb
    // cancels the borrow of D4.
    if b1 | b2 {
        qhat -= 1;
        let carry = add_assign(&mut w[..n], v);
        w[n] = w[n].wrapping_add(u64::from(carry));
    }
    qhat as u64
}
