use crate::interval::*;
use std::fmt;

#[cfg(test)]
mod diff_tests;
mod digits;

fn fmt_impl(x: Interval, d: Option<Decoration>, f: &mut fmt::Formatter, conv: char) -> fmt::Result {
    let width = f.width().unwrap_or(0);
    let str_width = 2 * width + 1;
    if d == Some(Decoration::Ill) {
        return write!(f, "[{:^w$}]", "nai", w = str_width);
    }
    let sd = match d {
        Some(Decoration::Com) => "_com",
        Some(Decoration::Dac) => "_dac",
        Some(Decoration::Def) => "_def",
        Some(Decoration::Trv) => "_trv",
        _ => "",
    };
    if x.is_empty() {
        write!(f, "[{:^w$}]{}", "empty", sd, w = str_width)
    } else if x.is_entire() {
        write!(f, "[{:^w$}]{}", "entire", sd, w = str_width)
    } else {
        write!(
            f,
            "[{:>w$},{:>w$}]{}",
            bound(x.inf(), f.precision(), conv, false),
            bound(x.sup(), f.precision(), conv, true),
            sd,
            w = width
        )
    }
}

// The bound `x` of a nonempty interval, rounded toward +∞ if `up` and toward -∞ otherwise, in
// the text that inari printed with MPFR before it had digits of its own: that of
// `mpfr::asprintf` with the template `%RUc` or `%RDc`, or `%.pRUc` or `%.pRDc` for the
// precision `prec = Some(p)`, for the conversion `c = conv` (`'f'`, `'e'` or `'a'`, as in C's
// `printf`), and `-inf` or `inf` for an infinite `x`. `src/format/diff_tests.rs` compares the
// text with MPFR's, and the one difference that it finds is `%.0RUa` and `%.0RDa` of a number
// of at most 4 significant bits, rounded away from zero: MPFR adds 1 to the digit though the
// number is exact, and writes a NUL for the digit 16, where `hex_text` keeps the digit.
fn bound(x: f64, prec: Option<usize>, conv: char, up: bool) -> String {
    debug_assert!(!x.is_nan());
    if x.is_infinite() {
        return String::from(if x < 0.0 { "-inf" } else { "inf" });
    }
    let mut s = String::new();
    // A minus sign for every negative number, -0 included, also where it rounds to zero, as
    // MPFR writes it.
    if x.is_sign_negative() {
        s.push('-');
    }
    match conv {
        'f' => fixed_text(&mut s, x, prec.unwrap_or(6), up),
        'e' => sci_text(&mut s, x, prec.unwrap_or(16), up),
        _ => hex_text(&mut s, x, prec, up),
    }
    s
}

// Appends `n` zeros.
fn push_zeros(s: &mut String, n: usize) {
    s.extend(std::iter::repeat_n('0', n));
}

// `|x|` as `%.pf` writes it: the digits before the point, and the point and `p` digits after it
// if `p > 0`.
fn fixed_text(s: &mut String, x: f64, p: usize, up: bool) {
    // The digits of `|x| * 10^p` rounded: `|x|` rounded is `d * 10^k` with `-p <= k <= 0`, so
    // they are those of `d` and `p + k` zeros.
    let mut ds = if x == 0.0 {
        String::from("0")
    } else {
        let (d, k) = digits::fixed(x, p, up);
        let mut ds = d.to_dec();
        push_zeros(&mut ds, p - k.unsigned_abs() as usize);
        ds
    };
    let n = ds.len();
    if n <= p {
        // `|x|` rounded is below 1, and the digits after the point are `ds` with zeros in front.
        s.push_str("0.");
        push_zeros(s, p - n);
        s.push_str(&ds);
    } else {
        let frac = ds.split_off(n - p);
        s.push_str(&ds);
        if p > 0 {
            s.push('.');
            s.push_str(&frac);
        }
    }
}

// `|x|` as `%.pe` writes it: `p + 1` significant digits, the point after the first if `p > 0`,
// and `e` and the exponent of ten of the first digit, with its sign and at least two digits.
fn sci_text(s: &mut String, x: f64, p: usize, up: bool) {
    let (ds, e) = if x == 0.0 {
        (String::from("0"), 0)
    } else {
        let (d, k) = digits::sci(x, p, up);
        let ds = d.to_dec();
        // `d * 10^k` has its first digit at the exponent `len - 1 + k`.
        let e = ds.len() as i64 - 1 + k;
        (ds, e)
    };
    // `ds` has at most `p + 1` digits, or is 1 and `p + 1` zeros if the rounding carried into
    // a new digit, of which the last zero goes.
    let ds = &ds[..ds.len().min(p.saturating_add(1))];
    s.push_str(&ds[..1]);
    if p > 0 {
        s.push('.');
        s.push_str(&ds[1..]);
        push_zeros(s, p - (ds.len() - 1));
    }
    s.push_str(&format!(
        "e{}{:02}",
        if e < 0 { '-' } else { '+' },
        e.unsigned_abs()
    ));
}

// `|x|` as `%a` or `%.pa` writes it: `0x`, the hex digits with the point after the first if
// there are more, and `p` and the exponent of two of the first digit, with its sign.
fn hex_text(s: &mut String, x: f64, prec: Option<usize>, up: bool) {
    s.push_str("0x");
    if x == 0.0 {
        s.push('0');
        if let Some(p) = prec.filter(|&p| p > 0) {
            s.push('.');
            push_zeros(s, p);
        }
        s.push_str("p+0");
        return;
    }
    let (d, k) = digits::hex(x, prec, up);
    let e = match prec {
        None => {
            // The 14 digits of `d`, without the zeros at the end, and without the point if no
            // digit is left after it.
            let ds = format!("{:x}", d);
            let rest = ds[1..].trim_end_matches('0');
            s.push_str(&ds[..1]);
            if !rest.is_empty() {
                s.push('.');
                s.push_str(rest);
            }
            k + 52
        }
        Some(0) if d == 16 => {
            // The rounding carried into a new digit, which MPFR writes as 1.
            s.push('1');
            k + 4
        }
        Some(0) => {
            s.push_str(&format!("{:x}", d));
            k
        }
        Some(p) => {
            // `nd` digits, after which MPFR writes zeros, as the 14 digits are exact.
            let nd = p.min(13) + 1;
            if d == 1 << (4 * nd) {
                // The rounding carried into a new digit, which MPFR writes as 1 and `p` zeros.
                s.push_str("1.");
                push_zeros(s, p);
                k + 4 * nd as i64
            } else {
                let ds = format!("{:x}", d);
                s.push_str(&ds[..1]);
                s.push('.');
                s.push_str(&ds[1..]);
                push_zeros(s, p - (nd - 1));
                k + 4 * (nd as i64 - 1)
            }
        }
    };
    s.push_str(&format!("p{:+}", e));
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_impl(*self, None, f, 'f')
    }
}

impl fmt::LowerExp for Interval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_impl(*self, None, f, 'e')
    }
}

impl fmt::LowerHex for Interval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_impl(*self, None, f, 'a')
    }
}

impl fmt::Display for DecInterval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_impl(self.x(), Some(self.d()), f, 'f')
    }
}

impl fmt::LowerExp for DecInterval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_impl(self.x(), Some(self.d()), f, 'e')
    }
}

impl fmt::LowerHex for DecInterval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_impl(self.x(), Some(self.d()), f, 'a')
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use DecInterval as DI;
    use Decoration as D;
    use Interval as I;

    #[test]
    fn format() {
        assert_eq!(
            format!("{}", const_interval!(f64::NEG_INFINITY, 0.0)),
            "[-inf,0.000000]"
        );
        assert_eq!(
            format!("{:e}", const_interval!(f64::NEG_INFINITY, 0.0)),
            "[-inf,0.0000000000000000e+00]"
        );
        assert_eq!(
            format!("{:x}", const_interval!(f64::NEG_INFINITY, 0.0)),
            "[-inf,0x0p+0]"
        );

        assert_eq!(
            format!("{}", const_interval!(0.0, f64::INFINITY)),
            "[-0.000000,inf]"
        );
        assert_eq!(
            format!("{:e}", const_interval!(0.0, f64::INFINITY)),
            "[-0.0000000000000000e+00,inf]"
        );
        assert_eq!(
            format!("{:x}", const_interval!(0.0, f64::INFINITY)),
            "[-0x0p+0,inf]"
        );

        assert_eq!(format!("{:.6}", I::PI), "[3.141592,3.141593]");
        assert_eq!(format!("{:.6e}", I::PI), "[3.141592e+00,3.141593e+00]");
        assert_eq!(format!("{:.6x}", I::PI), "[0x3.243f6ap+0,0x3.243f6bp+0]");
        assert_eq!(
            format!("{:.6}", DI::set_dec(I::PI, D::Com)),
            "[3.141592,3.141593]_com"
        );
        assert_eq!(
            format!("{:.6}", DI::set_dec(I::PI, D::Dac)),
            "[3.141592,3.141593]_dac"
        );
        assert_eq!(
            format!("{:.6}", DI::set_dec(I::PI, D::Def)),
            "[3.141592,3.141593]_def"
        );
        assert_eq!(
            format!("{:.6}", DI::set_dec(I::PI, D::Trv)),
            "[3.141592,3.141593]_trv"
        );

        assert_eq!(
            format!("{:15.6}", I::PI),
            "[       3.141592,       3.141593]"
        );
        assert_eq!(
            format!("{:15.6e}", I::PI),
            "[   3.141592e+00,   3.141593e+00]"
        );
        assert_eq!(
            format!("{:15.6x}", I::PI),
            "[  0x3.243f6ap+0,  0x3.243f6bp+0]"
        );

        macro_rules! check {
            ($($f:literal),*) => {$(
                assert_eq!(format!($f, I::EMPTY), "[empty]");
                assert_eq!(format!($f, I::ENTIRE), "[entire]");
                assert_eq!(format!($f, DI::EMPTY), "[empty]_trv");
                assert_eq!(format!($f, DI::ENTIRE), "[entire]_dac");
                assert_eq!(format!($f, DI::NAI), "[nai]");
            )*};
        }
        check!("{}", "{:e}", "{:x}");

        macro_rules! check {
            ($($f:literal),*) => {$(
                assert_eq!(format!($f, I::EMPTY), "[   empty   ]");
                assert_eq!(format!($f, I::ENTIRE), "[  entire   ]");
                assert_eq!(format!($f, DI::EMPTY), "[   empty   ]_trv");
                assert_eq!(format!($f, DI::ENTIRE), "[  entire   ]_dac");
                assert_eq!(format!($f, DI::NAI), "[    nai    ]");
            )*};
        }
        check!("{:5}", "{:5e}", "{:5x}");
    }
}
