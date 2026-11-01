use crate::{elementary::get_d, interval::*};
use gmp_mpfr_sys::{gmp, mpfr};
use nom::{
    branch::alt,
    bytes::complete::{tag_no_case, take_while},
    character::complete::{char, digit0, digit1, hex_digit0, hex_digit1, one_of, space0},
    combinator::{map, opt, recognize, value},
    sequence::{delimited, pair, preceded, separated_pair, tuple},
    IResult,
};
use rug::{Float, Integer, Rational};
use std::{cmp::Ordering, result, str::FromStr};

#[derive(Clone, Debug)]
struct ParseNumberError;

impl From<std::num::ParseIntError> for ParseNumberError {
    fn from(_: std::num::ParseIntError) -> Self {
        Self
    }
}

impl From<std::num::TryFromIntError> for ParseNumberError {
    fn from(_: std::num::TryFromIntError) -> Self {
        Self
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum InfSup {
    Inf,
    Sup,
}

impl InfSup {
    fn as_rnd_t(self) -> mpfr::rnd_t {
        // `rocq/theories/Model.v` transcribes this enum and this function for the proofs of
        // the conversions of this file in `rocq/theories/ParseRound.v`,
        // `rocq/theories/ParseHull.v`, `rocq/theories/ParseExact.v` and
        // `rocq/theories/ParseDec.v`, so it has to be updated along with them.
        match self {
            Self::Inf => mpfr::rnd_t::RNDD,
            Self::Sup => mpfr::rnd_t::RNDU,
        }
    }
}

/// An extended rational number.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Number {
    // `rocq/theories/Model.v` transcribes this enum, with `Rational` as Stdlib's `Q`, and
    // its derived `PartialOrd` for the proofs of the conversions of this file in
    // `rocq/theories/ParseRound.v`, `rocq/theories/ParseHull.v`,
    // `rocq/theories/ParseExact.v` and `rocq/theories/ParseDec.v`, so it has to be
    // updated along with them.
    NegInfinity,
    Rational(Rational),
    Infinity,
}

impl std::ops::Neg for Number {
    type Output = Self;

    fn neg(self) -> Self {
        // `rocq/theories/Model.v` transcribes this function as `number_neg`, and
        // `number_neg_correct` in `rocq/theories/ParseRound.v` shows that it negates the
        // reals that a bound bounds, so it has to be updated along with them.
        use Number::*;

        match self {
            NegInfinity => Infinity,
            Rational(r) => Rational(-r),
            Infinity => NegInfinity,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
enum NInterval {
    // `rocq/theories/Model.v` transcribes this enum, its derived `PartialEq` with `EMPTY`,
    // and `inf`, `sup` and `is_common_interval` below for the proofs of the conversions of
    // this file in `rocq/theories/ParseHull.v`, `rocq/theories/ParseExact.v` and
    // `rocq/theories/ParseDec.v`, so it has to be updated along with them.
    InfSup(Number, Number),
    Point(Number),
}

impl NInterval {
    const EMPTY: Self = Self::InfSup(Number::Infinity, Number::NegInfinity);
    const ENTIRE: Self = Self::InfSup(Number::NegInfinity, Number::Infinity);

    fn inf(&self) -> &Number {
        match self {
            Self::InfSup(x, _) => x,
            Self::Point(x) => x,
        }
    }

    fn is_common_interval(&self) -> bool {
        matches!(
            (self.inf(), self.sup()),
            (Number::Rational(_), Number::Rational(_))
        )
    }

    fn sup(&self) -> &Number {
        match self {
            Self::InfSup(_, x) => x,
            Self::Point(x) => x,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
struct DecNInterval {
    // `rocq/theories/Model.v` transcribes this struct and `new` below for the proofs of
    // `From<DecNInterval>` and `From<NInterval>` in `rocq/theories/ParseDec.v`, so it has
    // to be updated along with them. `set_dec` below, which only the grammar calls, is
    // not transcribed, but `dec_ninterval_ok` in `rocq/theories/Model.v` states what
    // `decorated_interval` gives with it.
    x: NInterval,
    d: Decoration,
}

impl DecNInterval {
    const EMPTY: Self = Self {
        x: NInterval::EMPTY,
        d: Decoration::Trv,
    };

    const NAI: Self = Self {
        x: NInterval::EMPTY,
        d: Decoration::Ill,
    };

    fn new(x: NInterval) -> Self {
        use Decoration::*;

        let d = if x == NInterval::EMPTY {
            Trv
        } else if !x.is_common_interval() {
            Dac
        } else {
            Com
        };

        Self { x, d }
    }

    fn set_dec(x: NInterval, d: Decoration) -> Self {
        use Decoration::*;

        if d == Ill {
            Self::NAI
        } else if x == NInterval::EMPTY {
            Self::EMPTY
        } else if d == Com && !x.is_common_interval() {
            Self { x, d: Dac }
        } else {
            Self { x, d }
        }
    }
}

impl From<ParseNumberError> for IntervalError {
    fn from(_: ParseNumberError) -> Self {
        Self {
            kind: IntervalErrorKind::PossiblyUndefinedOperation,
        }
    }
}

#[derive(Debug)]
struct NumberLiteral<'a>(char, UnsignedNumberLiteral<'a>);

#[derive(Clone, Debug)]
enum UnsignedNumberLiteral<'a> {
    DecFloat(&'a str, &'a str),
    HexFloat(&'a str, &'a str),
    Infinity,
    Rational(&'a str),
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum UncertainDirection {
    Both,
    Down,
    Up,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum UncertainRadius<'a> {
    HalfUlp,
    MultipleOfUlp(&'a str),
    Unbounded,
}

fn sign(s: &str) -> IResult<&str, char> {
    map(opt(one_of("+-")), |os| os.unwrap_or('+'))(s)
}

fn integer(s: &str) -> IResult<&str, &str> {
    recognize(pair(sign, digit1))(s)
}

fn dec_significand(s: &str) -> IResult<&str, &str> {
    alt((
        // "123", "123.", "123.456"
        recognize(pair(digit1, opt(pair(char('.'), digit0)))),
        // ".456"
        recognize(pair(char('.'), digit1)),
    ))(s)
}

fn hex_significand(s: &str) -> IResult<&str, &str> {
    alt((
        recognize(pair(hex_digit1, opt(pair(char('.'), hex_digit0)))),
        recognize(pair(char('.'), hex_digit1)),
    ))(s)
}

fn dec_exponent(s: &str) -> IResult<&str, &str> {
    map(opt(preceded(tag_no_case("e"), integer)), |opt_exp| {
        opt_exp.unwrap_or("0")
    })(s)
}

fn positive_natural(s: &str) -> IResult<&str, &str> {
    recognize(tuple((
        take_while(|c| c == '0'),
        one_of("123456789"),
        digit0,
    )))(s)
}

fn unsigned_number(s: &str) -> IResult<&str, UnsignedNumberLiteral<'_>> {
    alt((
        // rational
        map(
            recognize(separated_pair(digit1, char('/'), positive_natural)),
            UnsignedNumberLiteral::Rational,
        ),
        // hexadecimal float
        map(
            pair(
                preceded(tag_no_case("0x"), hex_significand),
                preceded(tag_no_case("p"), integer),
            ),
            |(m, e)| UnsignedNumberLiteral::HexFloat(m, e),
        ),
        // decimal float
        map(pair(dec_significand, dec_exponent), |(m, e)| {
            UnsignedNumberLiteral::DecFloat(m, e)
        }),
        // infinity
        value(
            UnsignedNumberLiteral::Infinity,
            pair(tag_no_case("inf"), opt(tag_no_case("inity"))),
        ),
    ))(s)
}

fn number(s: &str) -> IResult<&str, NumberLiteral<'_>> {
    map(pair(sign, unsigned_number), |(s, n)| NumberLiteral(s, n))(s)
}

fn uncertain_radius(s: &str) -> IResult<&str, UncertainRadius<'_>> {
    map(
        opt(alt((
            map(digit1, UncertainRadius::MultipleOfUlp),
            value(UncertainRadius::Unbounded, char('?')),
        ))),
        |r| r.unwrap_or(UncertainRadius::HalfUlp),
    )(s)
}

fn uncertain_direction(s: &str) -> IResult<&str, UncertainDirection> {
    map(
        opt(alt((
            value(UncertainDirection::Down, tag_no_case("d")),
            value(UncertainDirection::Up, tag_no_case("u")),
        ))),
        |d| d.unwrap_or(UncertainDirection::Both),
    )(s)
}

fn pow(base: u32, exp: i32) -> Rational {
    let i = Integer::from(Integer::u_pow_u(base, exp.unsigned_abs()));
    let mut r = Rational::from(i);
    if exp < 0 {
        r.recip_mut();
    }
    r
}

fn parse_hex_float(mant: &str, exp: &str) -> result::Result<Rational, ParseNumberError> {
    let e = exp.parse::<i32>()?;
    let mut parts = mant.split('.');
    let int_part = parts.next().unwrap();
    let frac_part = parts.next().unwrap_or_default();

    // 1 hex digit encodes 4 bin digits.
    let frac_bits = i32::try_from(frac_part.len())?
        .checked_mul(4)
        .ok_or(ParseNumberError)?;
    let log2_ulp = e.checked_sub(frac_bits).ok_or(ParseNumberError)?;
    let ulp = pow(2, log2_ulp);

    let i_str = [int_part, frac_part].concat();
    let i = Integer::parse_radix(i_str, 16).unwrap();
    Ok(Rational::from(i) * &ulp)
}

fn parse_dec_float_with_ulp(
    mant: &str,
    exp: &str,
) -> result::Result<(Rational, Rational), ParseNumberError> {
    let e = exp.parse::<i32>()?;
    let mut parts = mant.split('.');
    let int_part = parts.next().unwrap();
    let frac_part = parts.next().unwrap_or_default();

    // 123.456e7 -> 123456e4 (ulp == 1e4)
    let frac_digits = i32::try_from(frac_part.len())?;
    let log10_ulp = e.checked_sub(frac_digits).ok_or(ParseNumberError)?;
    let ulp = pow(10, log10_ulp);

    let i_str = [int_part, frac_part].concat();
    let i = Integer::parse_radix(i_str, 10).unwrap();
    Ok((Rational::from(i) * &ulp, ulp))
}

fn parse_dec_float(mant: &str, exp: &str) -> result::Result<Rational, ParseNumberError> {
    parse_dec_float_with_ulp(mant, exp).map(|(r, _)| r)
}

fn parse_rational(s: &str) -> Rational {
    unsafe {
        let mut r = Rational::new();
        let c_string = std::ffi::CString::new(s).unwrap();
        gmp::mpq_set_str(r.as_raw_mut(), c_string.as_ptr(), 10);
        gmp::mpq_canonicalize(r.as_raw_mut());
        r
    }
}

fn parse_unsigned_number(n: UnsignedNumberLiteral) -> result::Result<Number, ParseNumberError> {
    use UnsignedNumberLiteral::*;

    Ok(match n {
        DecFloat(m, e) => Number::Rational(parse_dec_float(m, e)?),
        HexFloat(m, e) => Number::Rational(parse_hex_float(m, e)?),
        Infinity => Number::Infinity,
        Rational(s) => Number::Rational(parse_rational(s)),
    })
}

fn parse_number(NumberLiteral(s, n): NumberLiteral) -> result::Result<Number, ParseNumberError> {
    let n = parse_unsigned_number(n)?;
    Ok(if s == '-' { -n } else { n })
}

fn parse_opt_number(
    n: Option<NumberLiteral>,
    infsup: InfSup,
) -> result::Result<Number, ParseNumberError> {
    match n {
        Some(n) => parse_number(n),
        _ => match infsup {
            InfSup::Inf => Ok(Number::NegInfinity),
            InfSup::Sup => Ok(Number::Infinity),
        },
    }
}

fn infsup_interval(s: &str) -> IResult<&str, Result<NInterval>> {
    map(
        separated_pair(
            opt(number),
            delimited(space0, char(','), space0),
            opt(number),
        ),
        |(na, nb)| {
            let a = parse_opt_number(na, InfSup::Inf)?;
            let b = parse_opt_number(nb, InfSup::Sup)?;
            // `ninterval_ok` in `rocq/theories/Model.v` states what this test and the other
            // rules of the grammar guarantee of the `NInterval`s that they return. It is
            // checked by reading, not proved, and the proofs of `From<DecNInterval>` and
            // `From<NInterval>` in `rocq/theories/ParseHull.v` and `rocq/theories/ParseDec.v`
            // assume it, so it has to be updated along with the grammar.
            if a <= b && a != Number::Infinity && b != Number::NegInfinity {
                Ok(NInterval::InfSup(a, b))
            } else {
                Err(IntervalError {
                    kind: IntervalErrorKind::UndefinedOperation,
                })
            }
        },
    )(s)
}

fn point_interval(s: &str) -> IResult<&str, Result<NInterval>> {
    map(number, |n| {
        let a = parse_number(n)?;
        match a {
            Number::Rational(_) => Ok(NInterval::Point(a)),
            _ => Err(IntervalError {
                kind: IntervalErrorKind::UndefinedOperation,
            }),
        }
    })(s)
}

fn bracket_interval(s: &str) -> IResult<&str, Result<NInterval>> {
    delimited(
        pair(char('['), space0),
        map(
            opt(alt((
                map(tag_no_case("empty"), |_| Ok(NInterval::EMPTY)),
                map(tag_no_case("entire"), |_| Ok(NInterval::ENTIRE)),
                infsup_interval,
                point_interval,
            ))),
            |x| x.unwrap_or(Ok(NInterval::EMPTY)),
        ),
        pair(space0, char(']')),
    )(s)
}

fn uncertain_bound(
    center: &Rational,
    radius_or_unbounded: &Option<Rational>,
    dir: UncertainDirection,
    infsup: InfSup,
) -> Number {
    let directions_match = dir == UncertainDirection::Both
        || dir == UncertainDirection::Down && infsup == InfSup::Inf
        || dir == UncertainDirection::Up && infsup == InfSup::Sup;

    if directions_match {
        match radius_or_unbounded {
            Some(radius) => match infsup {
                InfSup::Inf => Number::Rational(Rational::from(center - radius)),
                InfSup::Sup => Number::Rational(Rational::from(center + radius)),
            },
            None => match infsup {
                InfSup::Inf => Number::NegInfinity,
                InfSup::Sup => Number::Infinity,
            },
        }
    } else {
        Number::Rational(center.clone())
    }
}

fn uncertain_interval(s: &str) -> IResult<&str, Result<NInterval>> {
    map(
        separated_pair(
            recognize(pair(sign, dec_significand)),
            char('?'),
            tuple((uncertain_radius, uncertain_direction, dec_exponent)),
        ),
        |(n, (rad, dir, exp))| {
            let (center, ulp) = parse_dec_float_with_ulp(n, exp)?;
            let radius_or_unbounded = match rad {
                UncertainRadius::HalfUlp => Some(ulp / 2),
                UncertainRadius::MultipleOfUlp(x) => {
                    let xi = Integer::parse_radix(x, 10).unwrap();
                    Some(Rational::from(xi) * ulp)
                }
                UncertainRadius::Unbounded => None,
            };
            let a = uncertain_bound(&center, &radius_or_unbounded, dir, InfSup::Inf);
            let b = uncertain_bound(&center, &radius_or_unbounded, dir, InfSup::Sup);
            Ok(NInterval::InfSup(a, b))
        },
    )(s)
}

fn interval(s: &str) -> IResult<&str, Result<NInterval>> {
    alt((bracket_interval, uncertain_interval))(s)
}

fn decoration(s: &str) -> IResult<&str, Decoration> {
    use Decoration::*;

    alt((
        value(Com, tag_no_case("com")),
        value(Dac, tag_no_case("dac")),
        value(Def, tag_no_case("def")),
        value(Trv, tag_no_case("trv")),
    ))(s)
}

fn decorated_interval(s: &str) -> IResult<&str, Result<DecNInterval>> {
    alt((
        map(
            tuple((char('['), space0, tag_no_case("nai"), space0, char(']'))),
            |_| Ok(DecNInterval::NAI),
        ),
        map(
            pair(interval, opt(preceded(char('_'), decoration))),
            |pair| match pair {
                (Ok(x), None) => Ok(DecNInterval::new(x)),
                (Ok(x), Some(d)) => {
                    let xd = DecNInterval::set_dec(x, d);
                    // `dec_ninterval_ok` in `rocq/theories/Model.v` states what this test,
                    // `DecNInterval::new` and `DecNInterval::NAI` guarantee of the
                    // decorations of the `DecNInterval`s that the grammar returns: `com`
                    // only for an `x` whose bounds are both rationals, and only `trv` or
                    // `ill` for `NInterval::EMPTY`. It is checked by reading, not proved,
                    // except for `DecNInterval::new` (`dn_new_ok`), and the proof of
                    // `From<DecNInterval>` in `rocq/theories/ParseDec.v` assumes it, so it
                    // has to be updated along with the grammar.
                    if xd.d == d {
                        Ok(xd)
                    } else {
                        Err(IntervalError {
                            kind: IntervalErrorKind::UndefinedOperation,
                        })
                    }
                }
                (Err(e), _) if e.kind == IntervalErrorKind::PossiblyUndefinedOperation => {
                    Err(IntervalError { kind: e.kind })
                }
                _ => Err(IntervalError {
                    kind: IntervalErrorKind::UndefinedOperation,
                }),
            },
        ),
    ))(s)
}

#[derive(Debug)]
struct F64 {
    // `rocq/theories/Model.v` transcribes this struct for the proofs of the conversions of
    // this file, so it has to be updated along with them.
    f: f64,
    inexact: bool,
    overflow: bool,
}

// `set_q_ok` in `rocq/theories/Mpfr.v`, which the proof of `rational_to_f64` below assumes of
// `mpfr::set_q`, fails for MPFR 4.2.2 where C `long`, MPFR's `mpfr_prec_t` and
// `mpfr_exp_t`, has 32 bits, as on 32-bit targets and on 64-bit Windows. There,
// `MPFR_PREC_MAX` is `2^31 - 257`, and `mpfr_set_q` fails on a rational whose numerator or
// denominator has more bits than that, not counting its low zero limbs. MPFR's widest
// exponent range is then `[1 - 2^30, 2^30 - 1]`. Where GMP limbs have 64 bits, as on 64-bit
// Windows, `mpfr_set_q` can return the ternary value 0 for a rational that overflows or
// underflows that range, and where they have 32 bits, as on most 32-bit targets, it can give
// such a rational the sign of the number it overwrites rather than its own. So this refuses
// to compile unless `long` and limbs have 64 bits, where none of these can happen (see
// `set_q_ok`).
const _: () = assert!(
    std::mem::size_of::<mpfr::prec_t>() == 8 && gmp::NUMB_BITS == 64,
    "the feature `gmp` of inari needs a target where C `long` and GMP limbs have 64 bits; \
     where `long` has 32 bits, MPFR's `mpfr_set_q` fails on some rationals wider than \
     about 2^30 bits, and where limbs have 32 bits too, it can give one of huge or tiny \
     magnitude the wrong sign"
);

// `f()` at the exponent range of `rational_to_f64`, `emin = -1073` and `emax = 1024`: it saves
// MPFR's exponent range, sets it to that one, calls `f` and restores it. `mpfr_tests` calls
// it too, and `parse_ok` there checks the range during `f()` and after it.
// `rocq/theories/Model.v` transcribes this function as part of `rational_to_f64`, so it has
// to be updated along with it. The proof of `rational_to_f64` takes MPFR's exponent range to
// stay as this function sets it until it restores it. No other thread can change it in
// between where MPFR keeps it per thread, as the MPFR that `gmp-mpfr-sys` builds does, which
// `range_per_thread` in `src/elementary/mpfr_tests.rs` tests. A system MPFR built without
// thread-local storage, which the feature `use-system-libs` of `gmp-mpfr-sys` can link,
// keeps it global instead, and fails that test.
pub(crate) fn with_parse_range<T>(f: impl FnOnce() -> T) -> T {
    let (orig_emin, orig_emax) = unsafe { (mpfr::get_emin(), mpfr::get_emax()) };
    unsafe {
        mpfr::set_emin((f64::MIN_EXP - (f64::MANTISSA_DIGITS as i32) + 1).into());
        mpfr::set_emax(f64::MAX_EXP.into());
    }
    let x = f();
    unsafe {
        mpfr::set_emin(orig_emin);
        mpfr::set_emax(orig_emax);
    }
    x
}

// The MPFR calls of `rational_to_f64`: `r` rounded in the direction `rnd` to an MPFR number
// `f` of 53 bits with `mpfr::set_q`, then `f` set with `mpfr::subnormalize` to `r` rounded in
// the same direction to the numbers that an `f64` holds, which have fewer than 53 bits below
// `f64::MIN_POSITIVE`, and converted with `get_d`, all at the range that `with_parse_range`
// sets. It returns `f`, the ternary value of `mpfr::subnormalize` and the `f64`.
// `after_set_q` gets `f` and the ternary value after `mpfr::set_q`, for `parse_ok` in
// `mpfr_tests`, which calls MPFR through this function. `rational_to_f64` passes one that
// does nothing. `rocq/theories/Model.v` transcribes this function as part of
// `rational_to_f64`, so it has to be updated along with it.
pub(crate) fn round_rational(
    r: &Rational,
    rnd: mpfr::rnd_t,
    after_set_q: impl FnOnce(&Float, i32),
) -> (Float, i32, f64) {
    let mut f = Float::new(f64::MANTISSA_DIGITS);
    let (t, d) = with_parse_range(|| {
        let t = unsafe { mpfr::set_q(f.as_raw_mut(), r.as_raw(), rnd) };
        after_set_q(&f, t);
        let t = unsafe { mpfr::subnormalize(f.as_raw_mut(), t, rnd) };
        (t, get_d(&f, rnd))
    });
    (f, t, d)
}

// Proved correct in `rocq/theories/ParseRound.v` (`rational_to_f64_correct`), assuming what
// `rocq/theories/Mpfr.v` says of `mpfr::set_q`, `mpfr::subnormalize` and `mpfr::get_d` at
// the exponent range that `with_parse_range` sets (`parse_ok`): `f` is `r` rounded toward -∞
// for `Inf` and toward +∞ for `Sup` to an `f64`, `inexact` is false exactly when `r` is the
// value of a finite `f64`, and `overflow` is true exactly when `f` is infinite.
// `rocq/theories/Model.v` transcribes this function, with `round_rational` and
// `with_parse_range` inlined and the MPFR functions abstract, so it has to be updated along
// with it.
fn rational_to_f64(r: &Rational, infsup: InfSup) -> F64 {
    fn ternary_to_ordering(t: i32) -> Ordering {
        t.cmp(&0)
    }

    let (_, t, f) = round_rational(r, infsup.as_rnd_t(), |_, _| ());
    F64 {
        f,
        inexact: ternary_to_ordering(t) != Ordering::Equal,
        overflow: f.is_infinite(),
    }
}

// Proved correct in `rocq/theories/ParseRound.v` (`number_to_f64_correct`), under the
// assumptions of `rational_to_f64`: it returns `rational_to_f64` of a `Rational`, and an
// infinity as it is, neither inexact nor overflowed. `rocq/theories/Model.v` transcribes
// this function, so it has to be updated along with it.
fn number_to_f64(n: &Number, infsup: InfSup) -> F64 {
    match n {
        Number::NegInfinity => F64 {
            f: f64::NEG_INFINITY,
            inexact: false,
            overflow: false,
        },
        Number::Rational(r) => rational_to_f64(r, infsup),
        Number::Infinity => F64 {
            f: f64::INFINITY,
            inexact: false,
            overflow: false,
        },
    }
}

impl From<NInterval> for Interval {
    fn from(x: NInterval) -> Self {
        // Proved correct in `rocq/theories/ParseDec.v` (`from_ninterval_correct`) for the
        // portable backend, assuming what `rocq/theories/Mpfr.v` says of MPFR (`parse_ok`)
        // and that `x` is what the grammar can return (`ninterval_ok`): the tightest
        // interval that contains the reals of `x`. `from_ninterval_new` shows that
        // `From<DecNInterval>` of `DecNInterval::new(x)` is `DecInterval::new` of it.
        // `rocq/theories/Model.v` transcribes this function as
        // `DecInterval.from_ninterval`, also for the proof that every `Interval` that the
        // constructors and the proved operations make is `valid` (`rocq/theories/Valid.v`),
        // so it has to be updated along with it.
        DecInterval::from(DecNInterval::new(x)).x()
    }
}

impl From<DecNInterval> for DecInterval {
    fn from(DecNInterval { x, d }: DecNInterval) -> Self {
        // Proved correct in `rocq/theories/ParseDec.v` (`from_dec_ninterval_correct`) for
        // the portable backend, assuming what `rocq/theories/Mpfr.v` says of MPFR
        // (`parse_ok`) and that `x` and `d` are what the grammar can return
        // (`dec_ninterval_ok`): NaI if `d` is `ill`, and otherwise the tightest interval
        // that contains the reals of `x`, decorated `d`, except `dac` in place of `com` if
        // overflow occurred, that is, `x` is bounded and the result is not, as IEEE 1788's
        // textToInterval asks (§12.12.7 of the draft P1788/D9.5, §6.7.5 of the draft
        // P1788.1/D9.8). For a `com` literal, that holds exactly when
        // `a.overflow || b.overflow`.
        // `rocq/theories/Model.v` transcribes this function as
        // `DecInterval.from_dec_ninterval`, also for the proof that every `Interval` that
        // the constructors and the proved operations make is `valid`
        // (`rocq/theories/Valid.v`), so it has to be updated along with it.
        let a = number_to_f64(x.inf(), InfSup::Inf);
        let b = number_to_f64(x.sup(), InfSup::Sup);
        // The empty interval cannot be constructed with `Interval::try_from`.
        let x = Interval::try_from((a.f, b.f)).unwrap_or(Interval::EMPTY);
        let d = if a.overflow || b.overflow {
            d.min(Decoration::Dac)
        } else {
            d
        };
        Self::set_dec(x, d)
    }
}

impl FromStr for Interval {
    type Err = IntervalError;

    fn from_str(s: &str) -> Result<Self> {
        match interval(s) {
            Ok(("", x)) => match x {
                Ok(x) => Ok(Self::from(x)),
                Err(e) => Err(IntervalError { kind: e.kind }),
            },
            // Invalid syntax.
            _ => Err(IntervalError {
                kind: IntervalErrorKind::UndefinedOperation,
            }),
        }
    }
}

impl FromStr for DecInterval {
    type Err = IntervalError;

    fn from_str(s: &str) -> Result<Self> {
        match decorated_interval(s) {
            Ok(("", x)) => match x {
                Ok(x) => Ok(Self::from(x)),
                Err(e) => Err(IntervalError { kind: e.kind }),
            },
            _ => Err(IntervalError {
                kind: IntervalErrorKind::UndefinedOperation,
            }),
        }
    }
}

impl Interval {
    fn try_from_ninterval_exact(x: NInterval) -> Result<Self> {
        // Proved correct in `rocq/theories/ParseExact.v` (`try_from_ninterval_exact_correct`)
        // for the portable backend, assuming what `rocq/theories/Mpfr.v` says of MPFR
        // (`parse_ok`), for any `x`: `Ok` exactly when each bound of `x` is an infinity or
        // the value of a finite `f64`, and then of the interval that holds exactly the reals
        // of `x`, which is the tightest one, and `Err` otherwise. `rocq/theories/Model.v`
        // transcribes this function, also for the proof that every `Interval` that the
        // constructors and the proved operations make is `valid` (`rocq/theories/Valid.v`),
        // so it has to be updated along with it.
        let a = number_to_f64(x.inf(), InfSup::Inf);
        let b = number_to_f64(x.sup(), InfSup::Sup);
        let x = Self::try_from((a.f, b.f)).unwrap_or(Self::EMPTY);
        if a.inexact || b.inexact {
            Err(IntervalError {
                kind: IntervalErrorKind::UndefinedOperation,
            })
        } else {
            Ok(x)
        }
    }

    #[doc(hidden)]
    pub fn _try_from_str_exact(s: &str) -> Result<Self> {
        match interval(s) {
            Ok(("", x)) => match x {
                Ok(x) => Self::try_from_ninterval_exact(x),
                Err(e) => Err(IntervalError { kind: e.kind }),
            },
            _ => Err(IntervalError {
                kind: IntervalErrorKind::UndefinedOperation,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use Interval as I;
    use IntervalErrorKind::*;

    #[test]
    fn parse() {
        // Integer significands without a dot are not covered by ITF1788.
        assert_eq!(interval!("[123]").unwrap(), const_interval!(123.0, 123.0));
        assert_eq!(
            interval!("[0x123p0]").unwrap(),
            const_interval!(291.0, 291.0)
        );

        // Exponent == i32::MAX + 1.
        assert_eq!(
            interval!("[123e2147483648]").unwrap_err().kind(),
            PossiblyUndefinedOperation
        );
        assert_eq!(
            interval!("[0x123p2147483648]").unwrap_err().kind(),
            PossiblyUndefinedOperation
        );

        // Exponent == i32::MIN - 1.
        assert_eq!(
            interval!("[123e-2147483649]").unwrap_err().kind(),
            PossiblyUndefinedOperation
        );
        assert_eq!(
            interval!("[0x123p-2147483649]").unwrap_err().kind(),
            PossiblyUndefinedOperation
        );

        assert_eq!(
            dec_interval!("[123e2147483648]").unwrap_err().kind(),
            PossiblyUndefinedOperation
        );
        assert_eq!(
            dec_interval!("[123e2147483648]_com").unwrap_err().kind(),
            PossiblyUndefinedOperation
        );
    }

    #[test]
    fn try_from_str_exact() {
        assert_eq!(interval_exact!("[]").unwrap(), I::EMPTY);
        assert_eq!(interval_exact!("[Empty]").unwrap(), I::EMPTY);
        assert_eq!(interval_exact!("[Entire]").unwrap(), I::ENTIRE);
        assert_eq!(
            interval_exact!("[0.0, 1.0]").unwrap(),
            const_interval!(0.0, 1.0)
        );
        assert_eq!(
            interval_exact!("[0.0, 0.1]").unwrap_err().kind(),
            UndefinedOperation
        );
        assert_eq!(
            interval_exact!("[0.1, 1.0]").unwrap_err().kind(),
            UndefinedOperation
        );

        // The smallest positive subnormal number.
        let f = 5e-324;
        assert_eq!(
            interval_exact!("[0x0.0000000000001p-1022]").unwrap(),
            interval!(f, f).unwrap()
        );
        assert_eq!(
            interval_exact!("[0x0.0000000000000ffp-1022]")
                .unwrap_err()
                .kind(),
            UndefinedOperation
        );
        assert_eq!(
            interval_exact!("[0x0.000000000000101p-1022]")
                .unwrap_err()
                .kind(),
            UndefinedOperation
        );
        assert_eq!(
            interval_exact!("[0x0.0000000000001p-1023]")
                .unwrap_err()
                .kind(),
            UndefinedOperation
        );

        // The largest normal number.
        let f = f64::MAX;
        assert_eq!(
            interval_exact!("[0x1.fffffffffffffp+1023]").unwrap(),
            interval!(f, f).unwrap()
        );
        assert_eq!(
            interval_exact!("[0x1.ffffffffffffeffp+1023]")
                .unwrap_err()
                .kind(),
            UndefinedOperation
        );
        assert_eq!(
            interval_exact!("[0x1.fffffffffffff01p+1023]")
                .unwrap_err()
                .kind(),
            UndefinedOperation
        );
        assert_eq!(
            interval_exact!("[0x1.fffffffffffffp+1024]")
                .unwrap_err()
                .kind(),
            UndefinedOperation
        );

        assert_eq!(
            interval_exact!("[123e2147483648]").unwrap_err().kind(),
            PossiblyUndefinedOperation
        );
    }

    #[test]
    fn decorated_literal_decorations() {
        // Tests the paths of `decorated_interval` that `dec_ninterval_ok` in
        // `rocq/theories/Model.v` relies on: it decorates a literal `com` only if both its
        // bounds are rationals, and an empty one only `trv`, or `ill` for `[nai]`.
        for s in [
            "[1,inf]_com",
            "[-inf,1]_com",
            "[entire]_com",
            "[empty]_com",
            "[]_com",
            "1.0??u_com",
            "[empty]_dac",
            "[empty]_def",
            "[]_dac",
            "[]_def",
        ] {
            assert_eq!(
                dec_interval!(s).map_err(|e| e.kind()),
                Err(UndefinedOperation),
                "{s}"
            );
        }

        assert_eq!(
            dec_interval!("[1,2]_com").unwrap().decoration(),
            Decoration::Com
        );
        assert_eq!(
            dec_interval!("[1,inf]_dac").unwrap().decoration(),
            Decoration::Dac
        );
        let x = dec_interval!("[empty]_trv").unwrap();
        assert!(x.is_empty());
        assert_eq!(x.decoration(), Decoration::Trv);
        assert!(dec_interval!("[nai]").unwrap().is_nai());
    }
}
