use crate::{classify::*, const_interval, interval::*};
use gmp_mpfr_sys::mpfr;
use rug::Float;

// `rocq/theories/Model.v` transcribes the functions that this macro defines, as `mpfr_fn`
// of an abstract MPFR function, for the proofs of the functions of this file in
// `rocq/theories/Elem.v`, `rocq/theories/ClosedDom.v`, `rocq/theories/Atanh.v`,
// `rocq/theories/Cosh.v`, `rocq/theories/Cos.v`, `rocq/theories/Sin.v` and
// `rocq/theories/Tan.v`, and of `quadrant`, which calls `sin_rd` and `cos_ru`, in
// `rocq/theories/TrigQuad.v`, so it has to be updated along with it.
// `rocq/theories/Mpfr.v` states what those proofs assume of the MPFR functions and of
// `mpfr::get_d`.
macro_rules! mpfr_fn {
    ($mpfr_f:ident, $f_rd:ident, $f_ru:ident) => {
        fn $f_rd(x: f64) -> f64 {
            mpfr_fn!($mpfr_f(x, RNDD))
        }

        fn $f_ru(x: f64) -> f64 {
            mpfr_fn!($mpfr_f(x, RNDU))
        }
    };

    ($mpfr_f:ident($x:ident, $rnd:ident)) => {{
        let mut x = Float::with_val(f64::MANTISSA_DIGITS, $x);
        let rnd = mpfr::rnd_t::$rnd;
        unsafe {
            mpfr::$mpfr_f(x.as_raw_mut(), x.as_raw(), rnd);
            mpfr::get_d(x.as_raw(), rnd)
        }
    }};
}

// `rocq/theories/Model.v` transcribes the functions that this macro defines, as `mpfr_fn2`
// of an abstract MPFR function, for the proofs of `(Dec)Interval::atan2` in
// `rocq/theories/Atan2.v` and of `(Dec)Interval::pow` in `rocq/theories/Pow.v`, so it has
// to be updated along with it. `rocq/theories/Mpfr.v` states what those proofs assume of
// `mpfr::atan2`, `mpfr::pow` and `mpfr::get_d`.
macro_rules! mpfr_fn2 {
    ($mpfr_f:ident, $f_rd:ident, $f_ru:ident) => {
        fn $f_rd(x: f64, y: f64) -> f64 {
            mpfr_fn2!($mpfr_f(x, y, RNDD))
        }

        fn $f_ru(x: f64, y: f64) -> f64 {
            mpfr_fn2!($mpfr_f(x, y, RNDU))
        }
    };

    ($mpfr_f:ident($x:ident, $y:ident, $rnd:ident)) => {{
        let mut x = Float::with_val(f64::MANTISSA_DIGITS, $x);
        let y = Float::with_val(f64::MANTISSA_DIGITS, $y);
        let rnd = mpfr::rnd_t::$rnd;
        unsafe {
            mpfr::$mpfr_f(x.as_raw_mut(), x.as_raw(), y.as_raw(), rnd);
            mpfr::get_d(x.as_raw(), rnd)
        }
    }};
}

// `rocq/theories/Model.v` transcribes the functions that this macro defines, as `mpfr_fn_si`
// of an abstract MPFR function, with the `i32` `y` as an integer, which `y.into()` converts
// to a `c_long` exactly, for the proofs of `(Dec)Interval::powi` in `rocq/theories/Powi.v`,
// so it has to be updated along with it. `rocq/theories/Mpfr.v` states what those proofs
// assume of `mpfr::pow_si` and of `mpfr::get_d`.
macro_rules! mpfr_fn_si {
    ($mpfr_f:ident, $f_rd:ident, $f_ru:ident) => {
        fn $f_rd(x: f64, y: i32) -> f64 {
            mpfr_fn_si!($mpfr_f(x, y, RNDD))
        }

        fn $f_ru(x: f64, y: i32) -> f64 {
            mpfr_fn_si!($mpfr_f(x, y, RNDU))
        }
    };

    ($mpfr_f:ident($x:ident, $y:ident, $rnd:ident)) => {{
        let mut x = Float::with_val(f64::MANTISSA_DIGITS, $x);
        let rnd = mpfr::rnd_t::$rnd;
        unsafe {
            mpfr::$mpfr_f(x.as_raw_mut(), x.as_raw(), $y.into(), rnd);
            mpfr::get_d(x.as_raw(), rnd)
        }
    }};
}

mpfr_fn!(acos, acos_rd, acos_ru);
mpfr_fn!(acosh, acosh_rd, acosh_ru);
mpfr_fn!(asin, asin_rd, asin_ru);
mpfr_fn!(asinh, asinh_rd, asinh_ru);
mpfr_fn!(atan, atan_rd, atan_ru);
mpfr_fn2!(atan2, atan2_rd, atan2_ru);
mpfr_fn!(atanh, atanh_rd, atanh_ru);
mpfr_fn!(cos, cos_rd, cos_ru);
mpfr_fn!(cosh, cosh_rd, cosh_ru);
mpfr_fn!(exp, exp_rd, exp_ru);
mpfr_fn!(exp10, exp10_rd, exp10_ru);
mpfr_fn!(exp2, exp2_rd, exp2_ru);
mpfr_fn!(log, ln_rd, ln_ru);
mpfr_fn!(log10, log10_rd, log10_ru);
mpfr_fn!(log2, log2_rd, log2_ru);
mpfr_fn2!(pow, pow_rd, pow_ru);
mpfr_fn_si!(pow_si, pown_rd, pown_ru);
mpfr_fn!(sin, sin_rd, sin_ru);
mpfr_fn!(sinh, sinh_rd, sinh_ru);
mpfr_fn!(tan, tan_rd, tan_ru);
mpfr_fn!(tanh, tanh_rd, tanh_ru);

// `rocq/theories/Model.v` transcribes this function for the proofs of `(Dec)Interval::cos`
// and `(Dec)Interval::tan`, so it has to be updated along with it. `rem_euclid_2_int` in
// `rocq/theories/TrigReduce.v` shows that it returns `0.0` for an even integer and `1.0` for
// an odd one.
fn rem_euclid_2(x: f64) -> f64 {
    if 2.0 * (x / 2.0).floor() == x {
        0.0
    } else {
        1.0
    }
}

// `rocq/theories/Model.v` transcribes this function for the proofs of `(Dec)Interval::cos`,
// `(Dec)Interval::sin` and `(Dec)Interval::tan`, so it has to be updated along with it.
// `quadrant_correct` in `rocq/theories/TrigQuad.v` shows that it returns
// `floor(x / (π/2)) mod 4` for a finite `x`.
//
// Returns the quadrant `floor(x / (π/2)) mod 4` of a finite `x`, from the signs of `sin(x)`
// and `cos(x)`: `[0, π/2)` has `sin(x) >= 0` and `cos(x) > 0`, `[π/2, π)` has `sin(x) >= 0`
// and `cos(x) <= 0`, and so on, modulo 2π. MPFR rounds correctly, so `sin_rd(x) < 0.0`
// exactly when `sin(x) < 0`, and `cos_ru(x) > 0.0` exactly when `cos(x) > 0`, however close
// `x` is to a multiple of π/2. As π is irrational, no float is a multiple of π/2 other than
// 0, so `sin(x)` and `cos(x)` are never 0 where the quadrant would then be wrong.
fn quadrant(x: f64) -> f64 {
    let sin_neg = sin_rd(x) < 0.0;
    let cos_pos = cos_ru(x) > 0.0;
    match (sin_neg, cos_pos) {
        (false, true) => 0.0,
        (false, false) => 1.0,
        (true, false) => 2.0,
        (true, true) => 3.0,
    }
}

// `rocq/theories/Model.v` transcribes this function for the proofs of `(Dec)Interval::cos`,
// `(Dec)Interval::sin` and `(Dec)Interval::tan`, so it has to be updated along with it.
// `quadrants_correct` in `rocq/theories/TrigCount.v` shows what it returns.
//
// For finite `a <= b`, returns `(qa, n)`, where `qa` is `ka mod 4` and `n` is `kb - ka` if
// that is less than 4, and at least 4 otherwise, with `ka = floor(a / (π/2))` and
// `kb = floor(b / (π/2))`. The quadrants give `d = (kb - ka) mod 4`, so `kb - ka` is `d` or
// at least `d + 4`. In the first case, `b - a < (d + 1)π/2`, and in the second,
// `b - a > (d + 3)π/2`, and `2d + 3` lies between the two for `d <= 3`, more than 0.4 away
// from each, so `b - a`, rounded to nearest, tells them apart.
fn quadrants(a: f64, b: f64) -> (f64, f64) {
    let qa = quadrant(a);
    let d = (quadrant(b) - qa).rem_euclid(4.0);
    let n = if b - a <= 2.0 * d + 3.0 { d } else { d + 4.0 };
    (qa, n)
}

// `rocq/theories/Model.v` transcribes this function for the proofs of `(Dec)Interval::cos`,
// `(Dec)Interval::sin` and `(Dec)Interval::tan`, so it has to be updated along with it.
// `floors_exact_ok` in `rocq/theories/TrigCert.v` shows what it returns.
//
// For finite `a` and `b`, the floors `qa` and `qb` of the bounds of `[a, b] / c`, and a
// constant `c` (`Interval::PI` or `Interval::FRAC_PI_2`) that contains the number `c`,
// returns `true` only if `qa` and `qb` are `floor(a / c)` and `floor(b / c)`. It may
// return `false` when they are, if `a / c` or `b / c` is close to an integer. As
// `[a, b] / c` contains every `r / c`, `qa <= floor(a / c)`, and as `[a, a] / c` does too,
// `floor(a / c)` is at most the floor of its upper bound, so the two are equal if that is
// `qa`, and the same for `qb`.
fn floors_exact(a: f64, b: f64, qa: f64, qb: f64, c: Interval) -> bool {
    (Interval::with_infsup_raw(a, a) / c).sup_raw().floor() == qa
        && (Interval::with_infsup_raw(b, b) / c).inf_raw().floor() == qb
}

// Proved correct in `rocq/theories/Elem.v`, from `rocq/theories/LogDom.v`, for the portable
// backend, for `ln`, `log10` and `log2` and their decorated versions, assuming what
// `rocq/theories/Mpfr.v` says of MPFR. `rocq/theories/Model.v` transcribes the functions
// that this macro defines, so it has to be updated along with it.
macro_rules! impl_log {
    ($(#[$meta:meta])* $f:ident, $f_impl:ident, $f_rd:ident, $f_ru:ident) => {
        $(#[$meta])*
        #[must_use]
        pub fn $f(self) -> Self {
            self.$f_impl().0
        }

        #[allow(clippy::many_single_char_names)]
        fn $f_impl(self) -> (Self, Decoration) {
            // See the comment in atanh_impl.
            const DOM: Interval = const_interval!(0.0, f64::INFINITY);
            let x = self.intersection(DOM);

            let a = x.inf_raw();
            let b = x.sup_raw();
            if x.is_empty() || b <= 0.0 {
                return (Self::EMPTY, Decoration::Trv);
            }

            let y = Self::with_infsup_raw($f_rd(a), $f_ru(b));
            let d = if self.interior(DOM) {
                Decoration::Com
            } else {
                Decoration::Trv
            };
            (y, d)
        }
    };
}

// Proved correct in `rocq/theories/Elem.v`, from `rocq/theories/MonoInc.v`, for the
// portable backend, for `asinh`, `atan`, `exp`, `exp10`, `exp2`, `sinh` and `tanh` and
// their decorated versions, assuming what `rocq/theories/Mpfr.v` says of MPFR, and for the
// decorated versions of `atan`, `exp`, `exp10`, `exp2` and `tanh` also if `self` is `com`
// only when `self.x()` is common, which `rocq/theories/ComCommon.v` proves of every
// `DecInterval` that the library makes. `rocq/theories/Model.v` transcribes the function
// that this macro defines, so it has to be updated along with it.
macro_rules! impl_mono_inc {
    ($(#[$meta:meta])* $f:ident, $f_rd:ident, $f_ru:ident) => {
        $(#[$meta])*
        #[must_use]
        pub fn $f(self) -> Self {
            if self.is_empty() {
                return self;
            }

            Self::with_infsup_raw($f_rd(self.inf_raw()), $f_ru(self.sup_raw()))
        }
    };
}

impl Interval {
    /// Returns the inverse cosine of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain      | Range      |
    /// | ----------- | ---------- |
    /// | $\[-1, 1\]$ | $\[0, π\]$ |
    #[must_use]
    pub fn acos(self) -> Self {
        self.acos_impl().0
    }

    fn acos_impl(self) -> (Self, Decoration) {
        // Proved correct, with `Interval::acos` and `DecInterval::acos`, in
        // `rocq/theories/ClosedDom.v` for the portable backend, assuming what
        // `rocq/theories/Mpfr.v` says of MPFR. `rocq/theories/Model.v` transcribes this
        // function and `Interval::acos`, so it has to be updated along with them.
        const DOM: Interval = const_interval!(-1.0, 1.0);
        let x = self.intersection(DOM);

        if x.is_empty() {
            return (x, Decoration::Trv);
        }

        let y = Self::with_infsup_raw(acos_rd(x.sup_raw()), acos_ru(x.inf_raw()));
        let d = if self.subset(DOM) {
            Decoration::Com
        } else {
            Decoration::Trv
        };
        (y, d)
    }

    /// Returns the inverse hyperbolic cosine of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain    | Range     |
    /// | --------- | --------- |
    /// | $\[1, ∞)$ | $\[0, ∞)$ |
    #[must_use]
    pub fn acosh(self) -> Self {
        self.acosh_impl().0
    }

    fn acosh_impl(self) -> (Self, Decoration) {
        // Proved correct, with `Interval::acosh` and `DecInterval::acosh`, in
        // `rocq/theories/Elem.v`, from `rocq/theories/ClosedDom.v`, for the portable backend,
        // assuming what `rocq/theories/Mpfr.v` says of MPFR. `rocq/theories/Model.v`
        // transcribes this function and `Interval::acosh`, so it has to be updated along
        // with them.
        const DOM: Interval = const_interval!(1.0, f64::INFINITY);
        let x = self.intersection(DOM);

        if x.is_empty() {
            return (x, Decoration::Trv);
        }

        let y = Self::with_infsup_raw(acosh_rd(x.inf_raw()), acosh_ru(x.sup_raw()));
        let d = if self.subset(DOM) {
            Decoration::Com
        } else {
            Decoration::Trv
        };
        (y, d)
    }

    /// Returns the inverse sine of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain      | Range           |
    /// | ----------- | --------------- |
    /// | $\[-1, 1\]$ | $\[-π/2, π/2\]$ |
    #[must_use]
    pub fn asin(self) -> Self {
        self.asin_impl().0
    }

    fn asin_impl(self) -> (Self, Decoration) {
        // Proved correct, with `Interval::asin` and `DecInterval::asin`, in
        // `rocq/theories/Elem.v`, from `rocq/theories/ClosedDom.v`, for the portable backend,
        // assuming what `rocq/theories/Mpfr.v` says of MPFR. `rocq/theories/Model.v`
        // transcribes this function and `Interval::asin`, so it has to be updated along with
        // them.
        const DOM: Interval = const_interval!(-1.0, 1.0);
        let x = self.intersection(DOM);

        if x.is_empty() {
            return (x, Decoration::Trv);
        }

        let y = Self::with_infsup_raw(asin_rd(x.inf_raw()), asin_ru(x.sup_raw()));
        let d = if self.subset(DOM) {
            Decoration::Com
        } else {
            Decoration::Trv
        };
        (y, d)
    }

    impl_mono_inc!(
        /// Returns the inverse hyperbolic sine of `self`.
        ///
        /// The domain and the range of the point function are:
        ///
        /// | Domain | Range |
        /// | ------ | ----- |
        /// | $\R$   | $\R$  |
        asinh,
        asinh_rd,
        asinh_ru
    );
    impl_mono_inc!(
        /// Returns the inverse tangent of `self`.
        ///
        /// The domain and the range of the point function are:
        ///
        /// | Domain | Range         |
        /// | ------ | ------------- |
        /// | $\R$   | $(-π/2, π/2)$ |
        atan,
        atan_rd,
        atan_ru
    );

    /// Returns the angle of the point $(\rhs, \self)$ measured counterclockwise from the positive
    /// $x$-axis in the Euclidean plane.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain                | Range      |
    /// | --------------------- | ---------- |
    /// | $\R^2 ∖ \set{(0, 0)}$ | $(-π, π\]$ |
    #[must_use]
    pub fn atan2(self, rhs: Self) -> Self {
        self.atan2_impl(rhs).0
    }

    #[allow(clippy::many_single_char_names)]
    fn atan2_impl(self, rhs: Self) -> (Self, Decoration) {
        // Proved correct, with `Interval::atan2` and `DecInterval::atan2`, in
        // `rocq/theories/Atan2.v` for the portable backend, assuming what
        // `rocq/theories/Mpfr.v` says of MPFR, and for `DecInterval::atan2` also if `self`
        // and `rhs` are `com` only when their intervals are common, which
        // `rocq/theories/ComCommon.v` proves of every `DecInterval` that the library makes.
        // `rocq/theories/Model.v` transcribes this function and `Interval::atan2`, so it has
        // to be updated along with them.
        let (x, y) = (rhs, self);
        let a = x.inf_raw();
        let b = x.sup_raw();
        let c = y.inf_raw();
        let d = y.sup_raw();

        use IntervalClass2::*;
        match x.classify2(y) {
            E_E | E_M | E_N0 | E_N1 | E_P0 | E_P1 | E_Z | M_E | N0_E | N1_E | P0_E | P1_E | Z_E
            | Z_Z => (Self::EMPTY, Decoration::Trv),
            M_M | M_N0 | N0_M | N0_N0 => (
                Self::with_infsup_raw(-Self::PI.sup_raw(), Self::PI.sup_raw()),
                Decoration::Trv,
            ),

            // First quadrant
            P0_P0 => (
                Self::with_infsup_raw(0.0, Self::FRAC_PI_2.sup_raw()),
                Decoration::Trv,
            ),
            P0_P1 | P1_P0 | P1_P1 | P1_Z | Z_P1 => (
                Self::with_infsup_raw(atan2_rd(c, b), atan2_ru(d, a)),
                Decoration::Com,
            ),

            // First & second quadrant
            M_P0 | M_Z => (
                Self::with_infsup_raw(0.0, Self::PI.sup_raw()),
                Decoration::Trv,
            ),
            M_P1 => (
                Self::with_infsup_raw(atan2_rd(c, b), atan2_ru(c, a)),
                Decoration::Com,
            ),

            // Second quadrant
            N0_P0 => (
                Self::with_infsup_raw(Self::FRAC_PI_2.inf_raw(), Self::PI.sup_raw()),
                Decoration::Trv,
            ),
            N0_P1 | N1_P1 => (
                Self::with_infsup_raw(atan2_rd(d, b), atan2_ru(c, a)),
                Decoration::Com,
            ),
            N1_P0 => (
                Self::with_infsup_raw(atan2_rd(d, b), Self::PI.sup_raw()),
                Decoration::Dac,
            ),

            // Second & third quadrant
            //N0_M => See above.
            N1_M | N1_N0 => (
                Self::with_infsup_raw(-Self::PI.sup_raw(), Self::PI.sup_raw()),
                Decoration::Def,
            ),

            // Third quadrant
            //N0_N0 => See above.
            N0_N1 | N1_N1 => (
                Self::with_infsup_raw(atan2_rd(d, a), atan2_ru(c, b)),
                Decoration::Com,
            ),
            //N1_N0 => See above.

            // Third & fourth quadrant
            //M_N0 => See above.
            M_N1 => (
                Self::with_infsup_raw(atan2_rd(d, a), atan2_ru(d, b)),
                Decoration::Com,
            ),

            // Fourth quadrant
            P0_N0 => (
                Self::with_infsup_raw(-Self::FRAC_PI_2.sup_raw(), 0.0),
                Decoration::Trv,
            ),
            P0_N1 | P1_N0 | P1_N1 | Z_N1 => (
                Self::with_infsup_raw(atan2_rd(c, a), atan2_ru(d, b)),
                Decoration::Com,
            ),

            // Fourth & first quadrant
            P0_M | Z_M => (
                Self::with_infsup_raw(-Self::FRAC_PI_2.sup_raw(), Self::FRAC_PI_2.sup_raw()),
                Decoration::Trv,
            ),
            P1_M => (
                Self::with_infsup_raw(atan2_rd(c, a), atan2_ru(d, a)),
                Decoration::Com,
            ),

            // X axis
            //M_Z => See above.
            N0_Z => (Self::PI, Decoration::Trv),
            // The next case cannot be merged with N1_P0 unless we replace -0.0 with +0.0
            // since IEEE 754/MPFR's atan2 returns ±π for y = ±0.0, x < 0.0, while we want only +π.
            N1_Z => (Self::PI, Decoration::Dac),
            P0_Z => (Self::zero(), Decoration::Trv),
            //P1_Z => See above.

            // Y axis
            //Z_M => See above.
            Z_N0 => (-Self::FRAC_PI_2, Decoration::Trv),
            //Z_N1 => See above.
            Z_P0 => (Self::FRAC_PI_2, Decoration::Trv),
            //Z_P1 => See above.
        }
    }

    /// Returns the inverse hyperbolic tangent of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain    | Range |
    /// | --------- | ----- |
    /// | $(-1, 1)$ | $\R$  |
    #[must_use]
    pub fn atanh(self) -> Self {
        self.atanh_impl().0
    }

    #[allow(clippy::many_single_char_names)]
    fn atanh_impl(self) -> (Self, Decoration) {
        // Proved correct, with `Interval::atanh` and `DecInterval::atanh`, in
        // `rocq/theories/Atanh.v` for the portable backend, assuming what
        // `rocq/theories/Mpfr.v` says of MPFR. `rocq/theories/Model.v` transcribes this
        // function and `Interval::atanh`, so it has to be updated along with them.
        //
        // Mathematically, the domain of atanh is (-1.0, 1.0), not [-1.0, 1.0].
        // However, IEEE 754/MPFR's atanh returns ±infinity for ±1.0,
        // (and signals the divide-by-zero exception), so we will make use of that.
        const DOM: Interval = const_interval!(-1.0, 1.0);
        let x = self.intersection(DOM);

        let a = x.inf_raw();
        let b = x.sup_raw();
        if x.is_empty() || b <= -1.0 || a >= 1.0 {
            return (Self::EMPTY, Decoration::Trv);
        }

        let y = Self::with_infsup_raw(atanh_rd(a), atanh_ru(b));
        let d = if self.interior(DOM) {
            Decoration::Com
        } else {
            Decoration::Trv
        };
        (y, d)
    }

    /// Returns the cosine of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain | Range       |
    /// | ------ | ----------- |
    /// | $\R$   | $\[-1, 1\]$ |
    #[must_use]
    pub fn cos(self) -> Self {
        // Proved, with `DecInterval::cos`, in `rocq/theories/Cos.v` for the portable backend,
        // assuming what `rocq/theories/Mpfr.v` says of MPFR, also of `mpfr::sin`, which
        // `quadrant` calls: the result is the tightest interval that contains the image of
        // `self`, and `DecInterval::cos` decorates it as IEEE 1788
        // asks if `self` is `com` only when `self.x()` is common, which
        // `rocq/theories/ComCommon.v` proves of every `DecInterval` that the library makes.
        // `rocq/theories/TrigQuad.v`, `rocq/theories/TrigCount.v` and
        // `rocq/theories/TrigCert.v` prove what `quadrant`, `quadrants` and `floors_exact`
        // return. `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it. `max` and `min` may return either zero if both arguments are zeros,
        // so the model takes which one they return as an argument.
        if self.is_empty() {
            return self;
        }

        let a = self.inf_raw();
        let b = self.sup_raw();
        let q_nowrap = (self / Self::PI).floor();
        let qa = q_nowrap.inf_raw();
        let qb = q_nowrap.sup_raw();
        // n and q are valid for small values.
        let n = if a == b {
            // For strict test cases on huge values.
            0.0
        } else {
            qb - qa
        };
        let q = rem_euclid_2(qa);
        // `qa` and `qb` are at most and at least the floors of `a / π` and `b / π`. They are
        // those floors if `qa == qb`, or if `floors_exact` says so. If `a == b`, `n` is 0,
        // and either monotone result is the tightest, whatever `qa` is. If `b - a >= 8.0`,
        // `self` is at least 2π wide, so that the result is `[-1, 1]` in any case. Otherwise,
        // `q` and `n` come from the quadrants, as `floor(r / π) = floor(floor(r / (π/2)) / 2)`.
        let (q, n) = if n == 0.0 || b - a >= 8.0 || floors_exact(a, b, qa, qb, Self::PI) {
            (q, n)
        } else {
            let (qa, n) = quadrants(a, b);
            ((qa / 2.0).floor(), ((qa % 2.0 + n) / 2.0).floor())
        };

        if n == 0.0 {
            if q == 0.0 {
                // monotonically decreasing
                Self::with_infsup_raw(cos_rd(b), cos_ru(a))
            } else {
                // monotonically increasing
                Self::with_infsup_raw(cos_rd(a), cos_ru(b))
            }
        } else if n <= 1.0 {
            if q == 0.0 {
                // decreasing, then increasing
                Self::with_infsup_raw(-1.0, cos_ru(a).max(cos_ru(b)))
            } else {
                // increasing, then decreasing
                Self::with_infsup_raw(cos_rd(a).min(cos_rd(b)), 1.0)
            }
        } else {
            const_interval!(-1.0, 1.0)
        }
    }

    /// Returns the hyperbolic cosine of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain | Range     |
    /// | ------ | --------- |
    /// | $\R$   | $\[1, ∞)$ |
    #[must_use]
    pub fn cosh(self) -> Self {
        // Proved correct, with `DecInterval::cosh`, in `rocq/theories/Cosh.v` for the
        // portable backend, assuming what `rocq/theories/Mpfr.v` says of MPFR.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated along
        // with it. `(-a).max(b)` may return either zero if `-a` and `b` are zeros, so the
        // model takes which one it returns as an argument.
        if self.is_empty() {
            return self;
        }

        let a = self.inf_raw();
        let b = self.sup_raw();
        if b < 0.0 {
            Self::with_infsup_raw(cosh_rd(b), cosh_ru(a))
        } else if a > 0.0 {
            Self::with_infsup_raw(cosh_rd(a), cosh_ru(b))
        } else {
            Self::with_infsup_raw(1.0, cosh_ru((-a).max(b)))
        }
    }

    impl_mono_inc!(
        /// Returns `self` raised to the power of $\e$.
        ///
        /// The domain and the range of the point function are:
        ///
        /// | Domain | Range    |
        /// | ------ | -------- |
        /// | $\R$   | $(0, ∞)$ |
        exp,
        exp_rd,
        exp_ru
    );
    impl_mono_inc!(
        /// Returns `self` raised to the power of 10.
        ///
        /// The domain and the range of the point function are:
        ///
        /// | Domain | Range    |
        /// | ------ | -------- |
        /// | $\R$   | $(0, ∞)$ |
        exp10,
        exp10_rd,
        exp10_ru
    );
    impl_mono_inc!(
        /// Returns `self` raised to the power of 2.
        ///
        /// The domain and the range of the point function are:
        ///
        /// | Domain | Range    |
        /// | ------ | -------- |
        /// | $\R$   | $(0, ∞)$ |
        exp2,
        exp2_rd,
        exp2_ru
    );

    impl_log!(
        /// Returns the natural logarithm of `self`.
        ///
        /// The domain and the range of the point function are:
        ///
        /// | Domain   | Range |
        /// | -------- | ----- |
        /// | $(0, ∞)$ | $\R$  |
        ln,
        ln_impl,
        ln_rd,
        ln_ru
    );
    impl_log!(
        /// Returns the base-10 logarithm of `self`.
        ///
        /// The domain and the range of the point function are:
        ///
        /// | Domain   | Range |
        /// | -------- | ----- |
        /// | $(0, ∞)$ | $\R$  |
        log10,
        log10_impl,
        log10_rd,
        log10_ru
    );
    impl_log!(
        /// Returns the base-2 logarithm of `self`.
        ///
        /// The domain and the range of the point function are:
        ///
        /// | Domain   | Range |
        /// | -------- | ----- |
        /// | $(0, ∞)$ | $\R$  |
        log2,
        log2_impl,
        log2_rd,
        log2_ru
    );

    /// Returns `self` raised to the power of `rhs`.
    ///
    /// The point function is defined as follows:
    ///
    /// $$
    /// x^y = \begin{cases}
    ///   0           & \for x = 0 ∧ y > 0, \\\\
    ///   e^{y \ln x} & \for x > 0.
    ///  \end{cases}
    /// $$
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain                              | Range     |
    /// | ----------------------------------- | --------- |
    /// | $((0, ∞) × \R) ∪ (\set 0 × (0, ∞))$ | $\[0, ∞)$ |
    #[must_use]
    pub fn pow(self, rhs: Self) -> Self {
        self.pow_impl(rhs).0
    }

    #[allow(clippy::many_single_char_names)]
    fn pow_impl(self, rhs: Self) -> (Self, Decoration) {
        // Proved correct, with `Interval::pow` and `DecInterval::pow`, in
        // `rocq/theories/Pow.v` for the portable backend, assuming what `rocq/theories/Mpfr.v`
        // says of MPFR, and for `DecInterval::pow` also if `self` and `rhs` are `com` only
        // when their intervals are common, which `rocq/theories/ComCommon.v` proves of every
        // `DecInterval` that the library makes. `rocq/theories/Model.v` transcribes this
        // function and `Interval::pow`, so it has to be updated along with them. `min` and
        // `max` may return either zero if both arguments are zeros, so the model takes which
        // ones they return as arguments.
        const DOM: Interval = const_interval!(0.0, f64::INFINITY);
        let x = self.intersection(DOM);

        if x.either_empty(rhs) {
            return (Self::EMPTY, Decoration::Trv);
        }

        let a = x.inf_raw();
        let b = x.sup_raw();
        let c = rhs.inf_raw();
        let d = rhs.sup_raw();

        if d <= 0.0 {
            if b == 0.0 {
                return (Self::EMPTY, Decoration::Trv);
            }

            let dec = if self.interior(DOM) {
                Decoration::Com
            } else {
                Decoration::Trv
            };

            if b < 1.0 {
                (Self::with_infsup_raw(pow_rd(b, d), pow_ru(a, c)), dec)
            } else if a > 1.0 {
                (Self::with_infsup_raw(pow_rd(b, c), pow_ru(a, d)), dec)
            } else {
                (Self::with_infsup_raw(pow_rd(b, c), pow_ru(a, c)), dec)
            }
        } else if c > 0.0 {
            let dec = if self.subset(DOM) {
                Decoration::Com
            } else {
                Decoration::Trv
            };

            if b < 1.0 {
                (Self::with_infsup_raw(pow_rd(a, d), pow_ru(b, c)), dec)
            } else if a > 1.0 {
                (Self::with_infsup_raw(pow_rd(a, c), pow_ru(b, d)), dec)
            } else {
                (Self::with_infsup_raw(pow_rd(a, d), pow_ru(b, d)), dec)
            }
        } else {
            if b == 0.0 {
                return (Self::zero(), Decoration::Trv);
            }

            let z_ac = pow_ru(a, c);
            let z_ad = pow_rd(a, d);
            let z_bc = pow_rd(b, c);
            let z_bd = pow_ru(b, d);
            let dec = if self.interior(DOM) {
                Decoration::Com
            } else {
                Decoration::Trv
            };

            (Self::with_infsup_raw(z_ad.min(z_bc), z_ac.max(z_bd)), dec)
        }
    }

    /// Returns `self` raised to the power of `rhs`.
    ///
    /// The point functions are indexed by $n$, and are defined as follows:
    ///
    /// $$
    /// x^n = \begin{cases}
    ///   \overbrace{x × ⋯ × x}^{n \text{ copies}} & \for n > 0, \\\\
    ///   1          & \for n = 0, \\\\
    ///   1 / x^{-n} & \for n < 0.
    ///  \end{cases}
    /// $$
    ///
    /// The domains and the ranges of the point functions are:
    ///
    /// |                | Domain        | Range         |
    /// | -------------- | ------------- | ------------- |
    /// | $n > 0$, odd   | $\R$          | $\R$          |
    /// | $n > 0$, even  | $\R$          | $\[0, ∞)$     |
    /// | $n = 0$        | $\R$          | $\set 1$      |
    /// | $n < 0$, odd   | $\R ∖ \set 0$ | $\R ∖ \set 0$ |
    /// | $n < 0$, even  | $\R ∖ \set 0$ | $(0, ∞)$      |
    #[must_use]
    pub fn powi(self, rhs: i32) -> Self {
        self.powi_impl(rhs).0
    }

    fn powi_impl(self, rhs: i32) -> (Self, Decoration) {
        // Proved correct, with `Interval::powi` and `DecInterval::powi`, in
        // `rocq/theories/Powi.v` for the portable backend and every `rhs`, assuming what
        // `rocq/theories/Mpfr.v` says of MPFR, and for `DecInterval::powi` with `rhs <= 0`
        // also if `self` is `com` only when `self.x()` is common, which
        // `rocq/theories/ComCommon.v` proves of every `DecInterval` that the library makes.
        // `rocq/theories/Model.v` transcribes this function and `Interval::powi`, so it has
        // to be updated along with them.
        if self.is_empty() {
            return (self, Decoration::Trv);
        }

        let mut a = self.inf_raw();
        let mut b = self.sup_raw();

        #[allow(clippy::collapsible_else_if, clippy::collapsible_if)]
        if rhs < 0 {
            let d = if a <= 0.0 && b >= 0.0 {
                Decoration::Trv
            } else {
                Decoration::Com
            };

            if a == 0.0 && b == 0.0 {
                return (Self::EMPTY, d);
            }

            if rhs % 2 == 0 {
                let abs = self.abs();
                (
                    Self::with_infsup_raw(pown_rd(abs.sup_raw(), rhs), pown_ru(abs.inf_raw(), rhs)),
                    d,
                )
            } else {
                if a < 0.0 && b > 0.0 {
                    (Self::ENTIRE, d)
                } else {
                    if a == 0.0 {
                        a = 0.0; // [0, b]
                    }
                    if b == 0.0 {
                        b = -0.0; // [a, 0]
                    }
                    (Self::with_infsup_raw(pown_rd(b, rhs), pown_ru(a, rhs)), d)
                }
            }
        } else {
            if rhs % 2 == 0 {
                let abs = self.abs();
                (
                    Self::with_infsup_raw(pown_rd(abs.inf_raw(), rhs), pown_ru(abs.sup_raw(), rhs)),
                    Decoration::Com,
                )
            } else {
                (
                    Self::with_infsup_raw(pown_rd(a, rhs), pown_ru(b, rhs)),
                    Decoration::Com,
                )
            }
        }
    }

    /// Returns the sine of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain | Range       |
    /// | ------ | ----------- |
    /// | $\R$   | $\[-1, 1\]$ |
    #[must_use]
    pub fn sin(self) -> Self {
        // Proved, with `DecInterval::sin`, in `rocq/theories/Sin.v` for the portable backend,
        // assuming what `rocq/theories/Mpfr.v` says of MPFR, also of `mpfr::cos`, which
        // `quadrant` calls: the result is the tightest interval that contains the image of
        // `self`, and `DecInterval::sin` decorates it as IEEE 1788 asks if `self` is `com`
        // only when `self.x()` is common, which `rocq/theories/ComCommon.v` proves of every
        // `DecInterval` that the library makes. `rocq/theories/TrigQuad.v`,
        // `rocq/theories/TrigCount.v` and `rocq/theories/TrigCert.v` prove what `quadrant`,
        // `quadrants` and `floors_exact` return. `rocq/theories/Model.v` transcribes this
        // function, so it has to be updated along with it. `max` and `min` may return either
        // zero if both arguments are zeros, so the model takes which one they return as an
        // argument.
        if self.is_empty() {
            return self;
        }

        let a = self.inf_raw();
        let b = self.sup_raw();
        let q_nowrap = (self / Self::FRAC_PI_2).floor();
        let qa = q_nowrap.inf_raw();
        let qb = q_nowrap.sup_raw();
        let n = if a == b { 0.0 } else { qb - qa };
        let q = qa.rem_euclid(4.0);
        // As in `Interval::cos`, with π/2 in place of π.
        let (q, n) = if n == 0.0 || b - a >= 8.0 || floors_exact(a, b, qa, qb, Self::FRAC_PI_2) {
            (q, n)
        } else {
            quadrants(a, b)
        };

        if q == 0.0 && n < 1.0 || q == 3.0 && n < 2.0 {
            // monotonically increasing
            Self::with_infsup_raw(sin_rd(a), sin_ru(b))
        } else if q == 1.0 && n < 2.0 || q == 2.0 && n < 1.0 {
            // monotonically decreasing
            Self::with_infsup_raw(sin_rd(b), sin_ru(a))
        } else if q == 0.0 && n < 3.0 || q == 3.0 && n < 4.0 {
            // increasing, then decreasing
            Self::with_infsup_raw(sin_rd(a).min(sin_rd(b)), 1.0)
        } else if q == 1.0 && n < 4.0 || q == 2.0 && n < 3.0 {
            // decreasing, then increasing
            Self::with_infsup_raw(-1.0, sin_ru(a).max(sin_ru(b)))
        } else {
            const_interval!(-1.0, 1.0)
        }
    }

    impl_mono_inc!(
        /// Returns the hyperbolic sine of `self`.
        ///
        /// The domain and the range of the point function are:
        ///
        /// | Domain | Range |
        /// | ------ | ----- |
        /// | $\R$   | $\R$  |
        sinh,
        sinh_rd,
        sinh_ru
    );

    /// Returns the tangent of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain                            | Range |
    /// | --------------------------------- | ----- |
    /// | $\R ∖ \set{(n + 1/2) π ∣ n ∈ \Z}$ | $\R$  |
    #[must_use]
    pub fn tan(self) -> Self {
        self.tan_impl().0
    }

    fn tan_impl(self) -> (Self, Decoration) {
        // Proved, with `Interval::tan` and `DecInterval::tan`, in `rocq/theories/Tan.v` for
        // the portable backend, assuming what `rocq/theories/Mpfr.v` says of MPFR, also of
        // `mpfr::sin` and `mpfr::cos`, which `quadrant` calls: the result is the tightest
        // interval that contains the image of `self`, and `DecInterval::tan` decorates it as
        // IEEE 1788 asks. `rocq/theories/TrigQuad.v`,
        // `rocq/theories/TrigCount.v` and `rocq/theories/TrigCert.v` prove what `quadrant`,
        // `quadrants` and `floors_exact` return. `rocq/theories/Model.v` transcribes this
        // function and `Interval::tan`, so it has to be updated along with them.
        if self.is_empty() {
            return (self, Decoration::Trv);
        }

        let a = self.inf_raw();
        let b = self.sup_raw();
        let q_nowrap = (self / Self::FRAC_PI_2).floor();
        let qa = q_nowrap.inf_raw();
        let qb = q_nowrap.sup_raw();
        let n = if a == b { 0.0 } else { qb - qa };
        let q = rem_euclid_2(qa);

        let cont =
            qb != f64::INFINITY && b <= (Self::with_infsup_raw(qb, qb) * Self::FRAC_PI_2).inf_raw();
        // As in `Interval::cos`, with π/2 in place of π, and `self` at least π wide if
        // `b - a >= 4.0`. In the branches that read `cont`, `qb` is odd, so `cont` can be true
        // there only if `qb` is above the floor of `b / (π/2)`, and it is false for the floors
        // that come from the quadrants.
        let (q, n, cont) =
            if n == 0.0 || b - a >= 4.0 || floors_exact(a, b, qa, qb, Self::FRAC_PI_2) {
                (q, n, cont)
            } else {
                let (qa, n) = quadrants(a, b);
                (qa % 2.0, n, false)
            };
        if q == 0.0 && (n < 1.0 || n == 1.0 && cont) || q == 1.0 && (n < 2.0 || n == 2.0 && cont) {
            // In case of overflow, the decoration must be corrected by the caller.
            (Self::with_infsup_raw(tan_rd(a), tan_ru(b)), Decoration::Com)
        } else {
            (Self::ENTIRE, Decoration::Trv)
        }
    }

    impl_mono_inc!(
        /// Returns the hyperbolic tangent of `self`.
        ///
        /// The domain and the range of the point function are:
        ///
        /// | Domain | Range     |
        /// | ------ | --------- |
        /// | $\R$   | $(-1, 1)$ |
        tanh,
        tanh_rd,
        tanh_ru
    );
}

// `rocq/theories/Model.v` transcribes the functions that this macro defines, those for
// `cos`, `sin` and `tan` each on its own, as the model of `Interval::cos` and the others
// returns an `option`, for the proofs of the decorated versions of the functions of this
// file in `rocq/theories/Elem.v`, `rocq/theories/ClosedDom.v`, `rocq/theories/Atanh.v`,
// `rocq/theories/Cosh.v`, `rocq/theories/Cos.v`, `rocq/theories/Sin.v` and
// `rocq/theories/Tan.v`, so it has to be updated along with it.
macro_rules! impl_dec {
    ($f:ident) => {
        #[doc = concat!("The decorated version of [`Interval::", stringify!($f), "`].")]
        ///
        /// A NaI is returned if `self` is NaI.
        #[must_use]
        pub fn $f(self) -> Self {
            Self::set_dec(self.x().$f(), self.d())
        }
    };

    ($f:ident, $f_impl:ident) => {
        #[doc = concat!("The decorated version of [`Interval::", stringify!($f), "`].")]
        ///
        /// A NaI is returned if `self` is NaI.
        #[must_use]
        pub fn $f(self) -> Self {
            let (y, d) = self.x().$f_impl();
            Self::set_dec(y, self.d().min(d))
        }
    };
}

// `rocq/theories/Model.v` transcribes the functions that this macro defines, as
// `elem_dec2_impl` of `Interval::$f_impl` for the proof of `DecInterval::pow` in
// `rocq/theories/Pow.v`, and the one for `atan2` on its own, as the model of
// `Interval::atan2_impl` returns an `option`, for the proof of `DecInterval::atan2` in
// `rocq/theories/Atan2.v`, so it has to be updated along with it.
macro_rules! impl_dec2 {
    ($f:ident, $f_impl:ident) => {
        #[doc = concat!("The decorated version of [`Interval::", stringify!($f), "`].")]
        ///
        /// A NaI is returned if `self` or `rhs` is NaI.
        #[must_use]
        pub fn $f(self, rhs: Self) -> Self {
            let (z, d) = self.x().$f_impl(rhs.x());
            Self::set_dec(z, self.d().min(rhs.d().min(d)))
        }
    };
}

impl DecInterval {
    impl_dec!(acos, acos_impl);
    impl_dec!(acosh, acosh_impl);
    impl_dec!(asin, asin_impl);
    impl_dec!(asinh);
    impl_dec!(atan);
    impl_dec2!(atan2, atan2_impl);
    impl_dec!(atanh, atanh_impl);
    impl_dec!(cos);
    impl_dec!(cosh);
    impl_dec!(exp);
    impl_dec!(exp10);
    impl_dec!(exp2);
    impl_dec!(ln, ln_impl);
    impl_dec!(log10, log10_impl);
    impl_dec!(log2, log2_impl);
    impl_dec2!(pow, pow_impl);

    /// The decorated version of [`Interval::powi`].
    ///
    /// A NaI is returned if `self` is NaI.
    #[must_use]
    pub fn powi(self, rhs: i32) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proof of
        // `DecInterval::powi` in `rocq/theories/Powi.v` (see `Interval::powi_impl`), so it
        // has to be updated along with it.
        let (y, d) = self.x().powi_impl(rhs);
        Self::set_dec(y, self.d().min(d))
    }

    impl_dec!(sin);
    impl_dec!(sinh);
    impl_dec!(tan, tan_impl);
    impl_dec!(tanh);
}

#[cfg(test)]
mod tests {
    use crate::*;
    use DecInterval as DI;
    use Interval as I;

    #[test]
    fn nai() {
        assert!(DI::NAI.acos().is_nai());
        assert!(DI::NAI.acosh().is_nai());
        assert!(DI::NAI.asin().is_nai());
        assert!(DI::NAI.asinh().is_nai());
        assert!(DI::NAI.atan().is_nai());
        assert!(DI::NAI.atan2(DI::EMPTY).is_nai());
        assert!(DI::EMPTY.atan2(DI::NAI).is_nai());
        assert!(DI::NAI.atanh().is_nai());
        assert!(DI::NAI.cos().is_nai());
        assert!(DI::NAI.cosh().is_nai());
        assert!(DI::NAI.exp().is_nai());
        assert!(DI::NAI.exp10().is_nai());
        assert!(DI::NAI.exp2().is_nai());
        assert!(DI::NAI.ln().is_nai());
        assert!(DI::NAI.log10().is_nai());
        assert!(DI::NAI.log2().is_nai());
        assert!(DI::NAI.pow(DI::EMPTY).is_nai());
        assert!(DI::EMPTY.pow(DI::NAI).is_nai());
        assert!(DI::NAI.powi(1).is_nai());
        assert!(DI::NAI.sin().is_nai());
        assert!(DI::NAI.sinh().is_nai());
        assert!(DI::NAI.tan().is_nai());
        assert!(DI::NAI.tanh().is_nai());
    }

    // Arguments with a bound close to a multiple of π/2 relative to its magnitude, as every
    // bound above 2^53 is. For the first three and the narrow ones above 2^53, `sin`, `cos`
    // and `tan` were not the tightest before they reduced the argument exactly. The expected
    // bounds are the tightest, computed with MPFR at 2400 bits.
    #[test]
    fn trig_tightest() {
        let x = interval!(-134241567.2736211, -134241567.27362108).unwrap();
        assert_eq!(
            x.cos(),
            interval!(0.9999999999999989, 0.9999999999999999).unwrap()
        );

        let x = interval!(134246318.93250957, 134246318.9325096).unwrap();
        assert_eq!(
            x.sin(),
            interval!(0.9999999999999988, 0.9999999999999999).unwrap()
        );

        // Just above the pole 5π/2, and just below it and the pole 12345π/2.
        for (a, b, c, d) in [
            (
                7.853981633974484,
                7.853981633974485,
                -1718163698371049.0,
                -680181816043107.0,
            ),
            (
                7.853981633974482,
                7.853981633974483,
                837282432101130.8,
                3266247870639074.0,
            ),
            (
                19391.480654282994,
                19391.480654282997,
                200727993957.24622,
                744109987747.2866,
            ),
        ] {
            let x = DI::new(interval!(a, b).unwrap());
            let y = x.tan();
            assert_eq!(y.interval(), Some(interval!(c, d).unwrap()));
            assert_eq!(y.decoration(), Decoration::Com);
        }

        // Narrow arguments above 2^53, where the quadrants decide. They were `[-1, 1]`, and
        // `[-∞, +∞]` decorated `trv` for `tan`.
        let a = 2f64.powi(54);
        let x = interval!(a, a + 4.0).unwrap();
        assert_eq!(x.cos(), interval!(-1.0, 0.9675911762612261).unwrap());
        assert_eq!(x.sin(), interval!(-1.0, 0.8973347529975926).unwrap());
        let x = interval!(-a - 4.0, -a).unwrap();
        assert_eq!(x.sin(), interval!(-0.8973347529975926, 1.0).unwrap());
        let x = DI::new(interval!(15219727576813158.0, 15219727576813160.0).unwrap());
        let y = x.tan();
        assert_eq!(
            y.interval(),
            Some(interval!(-17.427922104255032, 0.5289263571245032).unwrap())
        );
        assert_eq!(y.decoration(), Decoration::Com);
    }

    #[test]
    fn tan() {
        // a, b ∈ (-π/2, π/2)
        assert!(interval!(std::f64::consts::FRAC_PI_4, I::FRAC_PI_2.inf())
            .unwrap()
            .tan()
            .is_common_interval());
        assert!(interval!(-std::f64::consts::FRAC_PI_4, I::FRAC_PI_2.inf())
            .unwrap()
            .tan()
            .is_common_interval());

        // a, b ∈ (-3π/2, -π/2)
        assert!(
            interval!(-3.0 * std::f64::consts::FRAC_PI_4, -I::FRAC_PI_2.sup())
                .unwrap()
                .tan()
                .is_common_interval()
        );
        assert!(
            interval!(-5.0 * std::f64::consts::FRAC_PI_4, -I::FRAC_PI_2.sup())
                .unwrap()
                .tan()
                .is_common_interval()
        );
    }
}
