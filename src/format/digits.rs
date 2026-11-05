// The digits of a finite nonzero bound of an interval that `src/format.rs` prints: the bound
// rounded in its direction, toward -∞ for the lower bound and toward +∞ for the upper one, to
// the digits that the style and the precision keep, as an integer times a power of the radix.
// `src/format.rs` writes the text from these, in MPFR's layout.
//
// `rocq/theories/Model.v` transcribes each function below for the proofs in
// `rocq/theories/FormatCut.v`, `rocq/theories/FormatDec.v` and `rocq/theories/FormatHex.v`,
// which show that `fixed`, `sci` and `hex` round as their comments say, so it has to be
// updated along with them. The proofs give the value of `d * 10^k` or `d * 2^k`, and
// `-p <= k <= 0` for `fixed`. The other bounds on `d` and `k` in the comments, on which the
// layout in `src/format.rs` relies, are not proved: `src/format/diff_tests.rs` compares the
// text with MPFR's.

use crate::nat::Nat;

// `|x| = m * 2^e` for a finite `x`, with `m < 2^53` the stored significand with the implicit
// bit.
fn decompose(x: f64) -> (u64, i64) {
    let c = x.to_bits() & !(1 << 63);
    let be = c >> 52;
    let m = c & ((1 << 52) - 1);
    // The implicit bit is 1 unless the biased exponent is 0, and the biased exponents 0 and 1
    // have the same scale.
    let m = if be == 0 { m } else { m + (1 << 52) };
    (m, be.max(1) as i64 - 1075)
}

// `|x| = n * 10^s` for a finite `x`, with `s <= 0`.
fn exact_dec(x: f64) -> (Nat, i64) {
    let (m, e) = decompose(x);
    let m = Nat::from_u64(m);
    if e >= 0 {
        (&m << e as u64, 0)
    } else {
        // m * 2^e = m * 5^-e * 10^e.
        (&m * &Nat::pow5(-e as u32), e)
    }
}

// Whether `x` rounds away from zero: toward +∞ (`up`) if it is positive, and toward -∞ if
// it is negative.
fn away(x: f64, up: bool) -> bool {
    x.is_sign_negative() != up
}

// `n * 10^s` cut to a multiple of `10^t`: `(d, max(s, t))` with `d * 10^max(s, t)` the result,
// rounded toward zero, or away from zero if `away`.
fn cut_dec(n: Nat, s: i64, t: i64, away: bool) -> (Nat, i64) {
    if t <= s {
        return (n, s);
    }
    let j = (t - s) as u32;
    let (q, r) = n.div_rem(&(&Nat::pow5(j) << u64::from(j)));
    if away && !r.is_zero() {
        (&q + &Nat::from_u64(1), t)
    } else {
        (q, t)
    }
}

// The precision from which `fixed` and `sci` keep every digit: `s >= -1074` in `exact_dec`,
// and `n` there has at most 767 digits, as `n < 2^1024` if `e >= 0` and
// `n < 2^53 * 5^1074 < 10^767` otherwise. Capping the precision there keeps it in an `i64`.
const ALL_DIGITS: usize = 1100;

/// `|x|` for `{:.p}`: `(d, k)` with `d * 10^k` the magnitude of `x` rounded to a multiple of
/// `10^-p`, toward -∞ for `x` if `up` is false, and toward +∞ otherwise, and `k >= -p`.
pub(super) fn fixed(x: f64, p: usize, up: bool) -> (Nat, i64) {
    let (n, s) = exact_dec(x);
    let t = -(p.min(ALL_DIGITS) as i64);
    cut_dec(n, s, t, away(x, up))
}

/// `|x|` for `{:.pe}`: `(d, k)` with `d * 10^k` the magnitude of `x` rounded to `p + 1`
/// significant digits, toward -∞ for `x` if `up` is false, and toward +∞ otherwise. `d` has
/// at most `p + 1` digits, or is `10^(p + 1)` if the rounding carries into a new digit.
pub(super) fn sci(x: f64, p: usize, up: bool) -> (Nat, i64) {
    let (n, s) = exact_dec(x);
    // The exponent of the last of the `p + 1` leading digits of `n * 10^s`.
    let t = n.digits10() as i64 + s - 1 - p.min(ALL_DIGITS) as i64;
    cut_dec(n, s, t, away(x, up))
}

// `m` cut to a multiple of `2^j` and divided by it, for `j < 64`: rounded toward zero, or away
// from zero if `away`.
fn cut_bin(m: u64, j: u32, away: bool) -> u64 {
    let q = m >> j;
    if away && m & ((1 << j) - 1) != 0 {
        q + 1
    } else {
        q
    }
}

/// `|x|` for `{:x}` with the precision `p`: `(d, k)` with `d * 2^k` the magnitude of `x`
/// rounded toward -∞ for `x` if `up` is false, and toward +∞ otherwise, to as many digits as
/// MPFR's `%Ra` writes:
/// - without a precision, exactly, with `d` the 14 hex digits that make `d * 2^k = |x|` with
///   `16^13 <= d < 16^14` and `k + 52` a multiple of 4;
/// - with `p = 0`, to 4 bits, with `8 <= d <= 16`;
/// - with `p >= 1`, to `p + 1` hex digits, with `k + 52` a multiple of 4: `d` has `p + 1`
///   digits, or is `16^(p + 1)` if the rounding carries into a new digit, for `p < 13`, and is
///   the exact `d` above otherwise.
pub(super) fn hex(x: f64, p: Option<usize>, up: bool) -> (u64, i64) {
    let (m, e) = decompose(x);
    // m * 2^e = m53 * 2^(ex - 52) with 2^52 <= m53 < 2^53 for x != 0: `ex` is the exponent
    // of the leading bit.
    let lz = m.leading_zeros() - 11;
    let m53 = m << lz;
    let ex = e + 52 - i64::from(lz);
    let away = away(x, up);
    if p == Some(0) {
        // The leading 4 bits, a multiple of 2^(ex - 3).
        return (cut_bin(m53, 49, away), ex - 3);
    }
    // The leading hex digit holds the bits of the exponents from `ex` down to
    // 4 * floor(ex / 4), so that it holds 1 to 4 bits and |x| = d14 * 2^(4 * floor(ex / 4) - 52)
    // with 16^13 <= d14 < 16^14.
    let d14 = m53 << ex.rem_euclid(4);
    let k = 4 * ex.div_euclid(4) - 52;
    match p {
        Some(p) if p < 13 => {
            // The leading `p + 1` of the 14 digits.
            let j = 4 * (13 - p as u32);
            (cut_bin(d14, j, away), k + i64::from(j))
        }
        _ => (d14, k),
    }
}
