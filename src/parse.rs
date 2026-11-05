use crate::{interval::*, nat::Nat, simd::round_up_exact};
use nom::{
    branch::alt,
    bytes::complete::{tag_no_case, take_while},
    character::complete::{char, digit0, digit1, hex_digit0, hex_digit1, one_of, space0},
    combinator::{map, opt, recognize, value},
    sequence::{delimited, pair, preceded, separated_pair, tuple},
    IResult,
};
use rat::Rat;
use std::{result, str::FromStr};

#[cfg(test)]
mod diff_tests;
mod rat;

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
    // `rocq/theories/Model.v` transcribes this enum for the proofs of the conversions of this
    // file in `rocq/theories/ParseRound.v`, `rocq/theories/ParseHull.v`,
    // `rocq/theories/ParseExact.v` and `rocq/theories/ParseDec.v`, so it has to be updated
    // along with them.
    Inf,
    Sup,
}

/// An extended rational number.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Number {
    // `rocq/theories/Model.v` transcribes this enum, and its derived `PartialOrd` with `Rat`
    // compared by value, for the proofs of the conversions of this file in
    // `rocq/theories/ParseRound.v`, `rocq/theories/ParseHull.v`,
    // `rocq/theories/ParseExact.v` and `rocq/theories/ParseDec.v`, so it has to be
    // updated along with them. That `impl Ord for Rat` compares by value is tested, not
    // proved.
    NegInfinity,
    Rational(Rat),
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
    // `rocq/theories/Model.v` transcribes this enum, `EMPTY` below, comparisons with it by
    // the derived `PartialEq`, and `inf`, `sup` and `is_common_interval` below for the
    // proofs of the conversions of this file and of the decorations that the grammar
    // gives in `rocq/theories/ParseHull.v`, `rocq/theories/ParseExact.v` and
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
    // `rocq/theories/Model.v` transcribes this struct, and `EMPTY`, `NAI` and `new` below,
    // for the proofs of `From<DecNInterval>` and `From<NInterval>` and of the decorations
    // that the grammar gives in `rocq/theories/ParseDec.v`, so it has to be updated along
    // with them.
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
        // `rocq/theories/Model.v` transcribes this function as `dn_set_dec`, and
        // `dn_set_dec_ok` in `rocq/theories/ParseDec.v` shows that it returns a
        // `DecNInterval` with `dec_ninterval_ok` for an `x` with `ninterval_ok` and any `d`,
        // so it has to be updated along with them.
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

fn parse_hex_float(mant: &str, exp: &str) -> result::Result<Rat, ParseNumberError> {
    let e = exp.parse::<i32>()?;
    let mut parts = mant.split('.');
    let int_part = parts.next().unwrap();
    let frac_part = parts.next().unwrap_or_default();

    // 1 hex digit encodes 4 bin digits.
    let frac_bits = i32::try_from(frac_part.len())?
        .checked_mul(4)
        .ok_or(ParseNumberError)?;
    let log2_ulp = e.checked_sub(frac_bits).ok_or(ParseNumberError)?;

    let i_str = [int_part, frac_part].concat();
    Ok(Rat {
        neg: false,
        num: Nat::from_hex(&i_str),
        den: Nat::from_u64(1),
        e2: log2_ulp,
        e5: 0,
    })
}

// The sign, the digits and the exponent `k` of the decimal `mant` `e` `exp`, whose value is
// `(-1)^neg * digits * 10^k`. `mant` can start with a sign in an uncertain interval.
fn parse_dec_float_with_ulp(
    mant: &str,
    exp: &str,
) -> result::Result<(bool, Nat, i32), ParseNumberError> {
    let e = exp.parse::<i32>()?;
    let (neg, mant) = match mant.strip_prefix('-') {
        Some(m) => (true, m),
        None => (false, mant.strip_prefix('+').unwrap_or(mant)),
    };
    let mut parts = mant.split('.');
    let int_part = parts.next().unwrap();
    let frac_part = parts.next().unwrap_or_default();

    // 123.456e7 -> 123456e4 (ulp == 1e4)
    let frac_digits = i32::try_from(frac_part.len())?;
    let log10_ulp = e.checked_sub(frac_digits).ok_or(ParseNumberError)?;

    let i_str = [int_part, frac_part].concat();
    Ok((neg, Nat::from_dec(&i_str), log10_ulp))
}

fn parse_dec_float(mant: &str, exp: &str) -> result::Result<Rat, ParseNumberError> {
    let (neg, num, k) = parse_dec_float_with_ulp(mant, exp)?;
    Ok(Rat {
        neg,
        num,
        den: Nat::from_u64(1),
        e2: k,
        e5: k,
    })
}

// The rational `p/q` of the literal `s`, where the grammar makes `q` positive.
fn parse_rational(s: &str) -> Rat {
    let (p, q) = s.split_once('/').unwrap();
    Rat {
        neg: false,
        num: Nat::from_dec(p),
        den: Nat::from_dec(q),
        e2: 0,
        e5: 0,
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
            // rules of the grammar guarantee of the `NInterval`s that they return, with
            // `number_ok` of each bound. It is checked by reading, not proved, and the proofs
            // of `From<DecNInterval>` and `From<NInterval>` and of the decorations that the
            // grammar gives, in `rocq/theories/ParseHull.v` and `rocq/theories/ParseDec.v`,
            // assume it, as the proof of `try_from_ninterval_exact` in
            // `rocq/theories/ParseExact.v` assumes `number_ok`, so it has to be updated along
            // with the grammar.
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

// `center` and the radius have the same `den`, `e2` and `e5`, which `add_same_scale` needs.
fn uncertain_bound(
    center: &Rat,
    radius_or_unbounded: &Option<Rat>,
    dir: UncertainDirection,
    infsup: InfSup,
) -> Number {
    let directions_match = dir == UncertainDirection::Both
        || dir == UncertainDirection::Down && infsup == InfSup::Inf
        || dir == UncertainDirection::Up && infsup == InfSup::Sup;

    if directions_match {
        match radius_or_unbounded {
            Some(radius) => match infsup {
                InfSup::Inf => Number::Rational(center.add_same_scale(&-radius.clone())),
                InfSup::Sup => Number::Rational(center.add_same_scale(radius)),
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
            let (neg, c, k) = parse_dec_float_with_ulp(n, exp)?;
            // The center is `(-1)^neg * c * 10^k`, and the radius `x * 10^k` or `10^k / 2`,
            // which are written over the same denominator, 1 or 2, so that their sum and
            // difference need no power of ten.
            let (c, den, radius) = match rad {
                UncertainRadius::HalfUlp => (&c << 1, Nat::from_u64(2), Some(Nat::from_u64(1))),
                UncertainRadius::MultipleOfUlp(x) => (c, Nat::from_u64(1), Some(Nat::from_dec(x))),
                UncertainRadius::Unbounded => (c, Nat::from_u64(1), None),
            };
            let radius_or_unbounded = radius.map(|r| Rat {
                neg: false,
                num: r,
                den: den.clone(),
                e2: k,
                e5: k,
            });
            let center = Rat {
                neg,
                num: c,
                den,
                e2: k,
                e5: k,
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
                    // This test rejects `[1,inf]_com` and `[empty]_dac`, which `set_dec`
                    // would decorate `dac` and `trv`. `rocq/theories/Model.v` transcribes
                    // this arm as `dn_decorated`, and `dn_decorated_ok` in
                    // `rocq/theories/ParseDec.v` shows that, for an `x` with `ninterval_ok`,
                    // the `xd` that it returns has the decoration `d`, the `NInterval` `x`
                    // unless `d` is `ill`, and `dec_ninterval_ok`, which the proof of
                    // `From<DecNInterval>` assumes, so it has to be updated along with them.
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

// What `rational_to_f64` computes of the magnitude `|x|` of a nonzero `Rat` `x` before it rounds
// it. `rocq/theories/Model.v` transcribes this enum for the proofs of `scale` and
// `round_up_scaled` in `rocq/theories/ParseScale.v` and `rocq/theories/ParseRound.v`, so it
// has to be updated along with them.
enum Scaled {
    // `|x| > 2^1024`.
    Huge,
    // `0 < |x| < 2^-1074`.
    Tiny,
    // `Mid(q, e, sticky)`: `|x| = (q + δ) * 2^e` with `2^55 <= q < 2^57`,
    // `-2^20 <= e <= 2^20` and `0 <= δ < 1`, where `δ > 0` exactly when `sticky`.
    // `round_up_exact` asks for the bound on `e` (`round_up_exact_pre` in
    // `rocq/theories/Spec.v`).
    Mid(u128, i32, bool),
}

// `|x|` of a nonzero `x` as a `Scaled`. It decides `Huge` and `Tiny` from the numbers of bits
// and the exponents, before it computes `5^|e5|`, so that it never computes a power of five
// for a literal whose exponent only puts it far outside the range of `f64`. Otherwise, the
// grammar makes `e5` 0 or `e2`, and then `|e5|` and the widths of the numbers below are at
// most linear in the length of the literal. Proved correct in `rocq/theories/ParseScale.v`
// (`scale_correct`) for a nonzero `x` that the grammar can make (`rat_ok`), assuming that its
// `Nat`s have no zero limb at the top, as the header of `src/nat.rs` says: it does not panic,
// and returns a `Scaled` that describes `|x|` as the comments of `Scaled` say.
// `rocq/theories/Model.v` transcribes this function, with each `Nat` as the integer that it
// holds and each operation of `Nat` as its loop on the limbs of that integer, for that proof
// and the one of `rational_to_f64` in `rocq/theories/ParseRound.v`, so it has to be updated
// along with them.
fn scale(x: &Rat) -> Scaled {
    let e2 = i128::from(x.e2);
    let e5 = i128::from(x.e5);
    // 2^(b - 1) <= num < 2^b for a nonzero `num` of b bits, and 4^k <= 5^k <= 8^k for
    // k >= 0, so 2^lo5 <= 5^e5 <= 2^hi5 and 2^(b0 - 1 + lo5) < |x| < 2^(b0 + 1 + hi5).
    let b0 = i128::from(x.num.bits()) - i128::from(x.den.bits()) + e2;
    let (lo5, hi5) = if e5 >= 0 {
        (2 * e5, 3 * e5)
    } else {
        (3 * e5, 2 * e5)
    };
    if b0 + lo5 >= 1025 {
        return Scaled::Huge;
    }
    if b0 + hi5 <= -1075 {
        return Scaled::Tiny;
    }
    // |x| = n / d * 2^e2.
    let p = Nat::pow5(x.e5.unsigned_abs());
    let (n, d) = if x.e5 >= 0 {
        (&x.num * &p, x.den.clone())
    } else {
        (x.num.clone(), &x.den * &p)
    };
    // 2^(b - 1) < |x| < 2^(b + 1).
    let b = i128::from(n.bits()) - i128::from(d.bits()) + e2;
    if b >= 1025 {
        return Scaled::Huge;
    }
    if b <= -1075 {
        return Scaled::Tiny;
    }
    // q = floor(|x| / 2^e) = floor(n * 2^sh / d), which is in [2^55, 2^57) as
    // 2^55 < |x| / 2^e < 2^57. `b` is in (-1075, 1025), so `e` is in (-1131, 969), within
    // the bounds of `Mid`, and `e2` is an `i32`, so `sh` and `-sh` fit a `u64`.
    let e = b - 56;
    let sh = e2 - e;
    let (q, r) = if sh >= 0 {
        (&n << sh as u64).div_rem(&d)
    } else {
        n.div_rem(&(&d << (-sh) as u64))
    };
    Scaled::Mid(q.low_u128(), e as i32, !r.is_zero())
}

// `(-1)^neg * |x|` rounded toward +∞ to an `f64`, for the `Scaled` `s` of `|x|`, by
// `round_up_exact` of `src/simd/generic.rs` for `Mid`. Proved correct in
// `rocq/theories/ParseRound.v` (`round_up_scaled_correct`) for a nonzero `x`, with `neg` true
// exactly when `x < 0`, and any `s` that describes `|x|` as the comments of `Scaled` say: it
// does not panic, and returns `(-1)^neg * |x|` rounded toward +∞, a zero with the sign of
// `x`. `rocq/theories/Model.v` transcribes this function, so it has to be updated along with
// it.
fn round_up_scaled(neg: bool, s: &Scaled) -> f64 {
    match *s {
        Scaled::Huge => {
            if neg {
                f64::MIN
            } else {
                f64::INFINITY
            }
        }
        // A tiny negative number rounds to -0, as `round_up_exact` rounds it.
        Scaled::Tiny => {
            if neg {
                -0.0
            } else {
                f64::from_bits(1)
            }
        }
        Scaled::Mid(q, e, sticky) => round_up_exact(neg, q, e, sticky),
    }
}

// Proved correct in `rocq/theories/ParseRound.v` (`rational_to_f64_correct`) for an `x` that
// the grammar can make (`rat_ok`), assuming that its `Nat`s have no zero limb at the top (see
// "What is assumed" in `rocq/README.md`): it does not panic, `f` is `x` rounded toward -∞ for
// `Inf` and toward +∞ for `Sup` to an `f64`, `inexact` is false exactly when `x` is the value
// of a finite `f64`, and `overflow` is true exactly when `f` is infinite. Rounding toward -∞ is
// `-round_up(-x)`, and `x` is the value of an `f64` exactly when its two roundings agree. A
// zero `x` gives +0, whatever `neg` is, as MPFR does, against which `src/parse/diff_tests.rs`
// tests this function. `rocq/theories/Model.v` transcribes this function, so it has to be
// updated along with it.
fn rational_to_f64(x: &Rat, infsup: InfSup) -> F64 {
    if x.num.is_zero() {
        return F64 {
            f: 0.0,
            inexact: false,
            overflow: false,
        };
    }
    let s = scale(x);
    let up = round_up_scaled(x.neg, &s);
    let down = -round_up_scaled(!x.neg, &s);
    let f = match infsup {
        InfSup::Inf => down,
        InfSup::Sup => up,
    };
    F64 {
        f,
        inexact: up != down,
        overflow: f.is_infinite(),
    }
}

// Proved correct in `rocq/theories/ParseRound.v` (`number_to_f64_correct`) for an `n` that
// the grammar can make (`number_ok`, which is `rat_ok` of a `Rational`), assuming that the
// `Nat`s of a `Rational` have no zero limb at the top: it does not panic, `f` is an infinity
// `n` as it is, and a `Rational` `n` rounded toward -∞ for `Inf` and toward +∞ for `Sup` to an
// `f64`, `inexact` is false exactly when `n` is an infinity or the value of a finite `f64`, and
// `overflow` is true exactly when `n` is a `Rational` that rounds to an infinity.
// `rocq/theories/Model.v` transcribes this function, so it has to be updated along with it.
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
        // portable backend, assuming that `x` is what the grammar can return
        // (`ninterval_ok`, with `number_ok` of its bounds) and that the `Nat`s of its bounds
        // have no zero limb at the top: the tightest interval that contains the reals of `x`.
        // `from_ninterval_new` shows that `From<DecNInterval>` of `DecNInterval::new(x)` is
        // `DecInterval::new` of it.
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
        // the portable backend, assuming that `x` and `d` are what the grammar can return
        // (`dec_ninterval_ok`, with `number_ok` of the bounds of `x`) and that the `Nat`s of
        // the bounds of `x` have no zero limb at the top: NaI if `d` is `ill`, and otherwise
        // the tightest interval that contains the reals of `x`, decorated `d`, except `dac` in
        // place of `com` if overflow occurred, that is, `x` is bounded and the result is not,
        // as IEEE 1788's textToInterval asks (§12.12.7 of the draft P1788/D9.5, §6.7.5 of the
        // draft P1788.1/D9.8). For a `com` literal, that holds exactly when
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
        // for the portable backend, for any `x` whose bounds the grammar can make
        // (`number_ok`), assuming that the `Nat`s of its bounds have no zero limb at the top:
        // `Ok` exactly when each bound of `x` is an infinity or the value of a finite `f64`,
        // and then of the interval that holds exactly the reals of `x`, which is the tightest
        // one, and `Err` otherwise.
        // `rocq/theories/Model.v` transcribes this function, also for the proof that every
        // `Interval` that the constructors and the proved operations make is `valid`
        // (`rocq/theories/Valid.v`), so it has to be updated along with it.
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
        // `rocq/theories/Model.v` relies on, through the `nom` combinators: it decorates a
        // literal `com` only if both its bounds are rationals, `ill` only if it is `[nai]`,
        // and an empty one other than `[nai]` only `trv`.
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
            "[1,2]_ill",
            "[empty]_ill",
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
