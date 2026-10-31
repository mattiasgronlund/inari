// `DecInterval` has a module of its own, which declares no module, so that its fields are
// private to this file. The compiler then rejects, anywhere else, a struct expression of
// `DecInterval` under any name of the type (an alias, `Self` or a renaming `use`), and an
// assignment to one of its fields. The rest of the library reads the fields with `x()` and
// `d()`, and makes a `DecInterval` with `new_unchecked`, apart from the `transmute` in
// `const_dec_interval!`.
use crate::interval::*;

/// The decorated version of [`Interval`].
///
/// ## Notes on equality comparison
///
/// By definition, a NaI is *not* equal to itself:
///
/// ```
/// use inari::*;
/// assert_ne!(DecInterval::NAI, DecInterval::NAI);
/// ```
///
/// For this reason, the traits [`Eq`] and [`Hash`] are not implemented for the type.
///
/// [`Hash`]: std::hash::Hash
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct DecInterval {
    // `rocq/theories/ComCommon.v` proves that every `DecInterval` is `com` only if its
    // interval is common, for each place that makes one: the callers of `new_unchecked`
    // and `const_dec_interval!`. The proof that every `Interval` that the constructors and
    // the proved operations make is `valid` (`rocq/theories/Valid.v`) covers the interval
    // of a `DecInterval` too. Both rely on no code assigning to these fields. The fields
    // have no `pub`, so the compiler rejects an assignment to one outside this file, and
    // this file neither assigns to one nor takes a mutable reference to one.
    x: Interval,
    d: Decoration,
}

impl DecInterval {
    pub(crate) const fn new_unchecked(x: Interval, d: Decoration) -> Self {
        // The compiler confines struct expressions of `DecInterval` to this file, as its
        // fields are private, and this is the only one in it. `rocq/theories/Model.v`
        // transcribes this function and each of its callers for the proof that every
        // `DecInterval` is `com` only if its interval is common (`rocq/theories/ComCommon.v`),
        // and for the proof that every `Interval` that the constructors and the proved
        // operations make is `valid` (`rocq/theories/Valid.v`), so a new caller needs a proof
        // in both files. The proofs that the constants of `DecInterval` from `E` to `TAU` are
        // the tightest intervals around their values (`rocq/theories/ConstPi.v`,
        // `ConstInv.v`, `ConstLn.v` and `ConstLog.v`) use it too.
        Self { x, d }
    }

    /// Returns the interval part of `self`, also if `self` is NaI, unlike
    /// [`DecInterval::interval`].
    pub(crate) const fn x(self) -> Interval {
        // `rocq/theories/Model.v` transcribes this function as `itv`, the field that it
        // returns, for the proofs of `DecInterval::abs`, `DecInterval::add`,
        // `DecInterval::cancel_minus`, `DecInterval::cancel_plus`, `DecInterval::ceil`,
        // `DecInterval::div`, `DecInterval::floor`, `DecInterval::max`, `DecInterval::min`,
        // `DecInterval::mul`, `DecInterval::mul_add`, `DecInterval::mul_rev_to_pair`,
        // `DecInterval::neg`, `DecInterval::recip`, `DecInterval::round`,
        // `DecInterval::round_ties_even`, `DecInterval::sign`, `DecInterval::sqr`,
        // `DecInterval::sqrt`, `DecInterval::sub` and `DecInterval::trunc` and of the
        // decorated versions of the functions of `src/elementary.rs` in
        // `rocq/theories/Elem.v`, `rocq/theories/ClosedDom.v`, `rocq/theories/Atanh.v`,
        // `rocq/theories/Cosh.v`, `rocq/theories/Cos.v`, `rocq/theories/Sin.v`,
        // `rocq/theories/Tan.v`, `rocq/theories/Pow.v`, `rocq/theories/Powi.v` and
        // `rocq/theories/Atan2.v`, of `From<NInterval>` of `Interval` in
        // `rocq/theories/ParseDec.v`, for the proof that every `DecInterval` is `com` only if
        // its interval is common (`rocq/theories/ComCommon.v`), and for the proof that every
        // `Interval` that the constructors and the proved operations make is `valid`
        // (`rocq/theories/Valid.v`), so it has to be updated along with it.
        self.x
    }

    /// Returns the decoration part of `self`.
    pub(crate) const fn d(self) -> Decoration {
        // `rocq/theories/Model.v` transcribes this function as `dec`, the field that it
        // returns, for the proofs of `DecInterval::abs`, `DecInterval::add`,
        // `DecInterval::cancel_minus`, `DecInterval::cancel_plus`, `DecInterval::ceil`,
        // `DecInterval::div`, `DecInterval::floor`, `DecInterval::max`, `DecInterval::min`,
        // `DecInterval::mul`, `DecInterval::mul_add`, `DecInterval::mul_rev_to_pair`,
        // `DecInterval::neg`, `DecInterval::recip`, `DecInterval::round`,
        // `DecInterval::round_ties_even`, `DecInterval::sign`, `DecInterval::sqr`,
        // `DecInterval::sqrt`, `DecInterval::sub` and `DecInterval::trunc` and of the
        // decorated versions of the functions of `src/elementary.rs` in
        // `rocq/theories/Elem.v`, `rocq/theories/ClosedDom.v`, `rocq/theories/Atanh.v`,
        // `rocq/theories/Cosh.v`, `rocq/theories/Cos.v`, `rocq/theories/Sin.v`,
        // `rocq/theories/Tan.v`, `rocq/theories/Pow.v`, `rocq/theories/Powi.v` and
        // `rocq/theories/Atan2.v`, for the proof that every `DecInterval` is `com` only if
        // its interval is common (`rocq/theories/ComCommon.v`), and for the proof that every
        // `Interval` that the constructors and the proved operations make is `valid`
        // (`rocq/theories/Valid.v`), so it has to be updated along with it.
        self.d
    }
}
