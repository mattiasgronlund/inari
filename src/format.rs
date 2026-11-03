use crate::{interval::*, mpfr_calls::fmt_bounds};
use std::fmt;

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
        fmt_bounds(x.inf(), x.sup(), f.precision(), conv, |sa, sb| {
            write!(f, "[{:>w$},{:>w$}]{}", sa, sb, sd, w = width)
        })
    }
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
