use crate::{classify::*, interval::*, simd::*};
use std::{cmp::Ordering, unreachable};

// NOTE: `neg`, `add`, `sub`, `mul` and `div` are implemented in arith.rs

impl Interval {
    // Division functions [a, b] / [c, d] for various cases, shared
    // between `mul_rev_to_pair` (below) and `Div` (in arith.rs).
    #[inline]
    pub(crate) fn div_m_n1(self, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proofs of
        // `(Dec)Interval::div` and `(Dec)Interval::mul_rev_to_pair`, so it has to be updated
        // along with it.
        // M / N1 => [b/d, a/d] = [-b/d; a/d] = [b/-d; -a/-d] = [b; -a] ./ [-d; -d]
        let x = swap(self.rep); // [b; -a]
        let y = swap(rhs.rep); // [d; -c]
        let y = neg0(y); // [-d; -c]
        let y = shuffle02(y, y); // [-d; -d]
        Self { rep: div_ru(x, y) }
    }

    #[inline]
    pub(crate) fn div_m_p1(self, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proofs of
        // `(Dec)Interval::div` and `(Dec)Interval::mul_rev_to_pair`, so it has to be updated
        // along with it.
        // M / P1 => [a/c, b/c] = [-a/c; b/c] = [-a; b] ./ [c; c]
        let x = self.rep; // [-a; b]
        let y = neg0(rhs.rep); // [c; d]
        let y = shuffle02(y, y); // [c; c]
        Self { rep: div_ru(x, y) }
    }

    #[inline]
    pub(crate) fn div_n_n0(self, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proofs of
        // `(Dec)Interval::div` and `(Dec)Interval::mul_rev_to_pair`, so it has to be updated
        // along with it.
        // N / N0 => [b/c, +∞] = [-b/c; +∞] = [b/-c; +∞]
        let x = swap(self.rep); // [b; -a]
        let y = rhs.rep; // [-c; d]
        Self {
            rep: shuffle02(div_ru(x, y), splat(f64::INFINITY)),
        }
    }

    #[inline]
    pub(crate) fn div_n_n1(self, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proofs of
        // `(Dec)Interval::div` and `(Dec)Interval::mul_rev_to_pair`, so it has to be updated
        // along with it.
        // N / N1 => [b/c, a/d] = [-b/c; a/d] = [b/-c; a/d] = [b; a] ./ [-c; d]
        let x = neg0(self.rep); // [a; b]
        let x = swap(x); // [b; a]
        let y = rhs.rep; // [-c; d]
        Self { rep: div_ru(x, y) }
    }

    #[inline]
    pub(crate) fn div_n_p0(self, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proofs of
        // `(Dec)Interval::div` and `(Dec)Interval::mul_rev_to_pair`, so it has to be updated
        // along with it.
        // N / P0 => [-∞, b/d] = [+∞; b/d]
        let x = self.rep; // [-a; b]
        let y = rhs.rep; // [-c; d]
        Self {
            rep: shuffle03(splat(f64::INFINITY), div_ru(x, y)),
        }
    }

    #[inline]
    pub(crate) fn div_n_p1(self, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proofs of
        // `(Dec)Interval::div` and `(Dec)Interval::mul_rev_to_pair`, so it has to be updated
        // along with it.
        // N / P1 => [a/c, b/d] = [-a/c; b/d] = [-a; b] ./ [c; d]
        let x = self.rep; // [-a; b]
        let y = neg0(rhs.rep); // [c; d]
        Self { rep: div_ru(x, y) }
    }

    #[inline]
    pub(crate) fn div_p_n0(self, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proofs of
        // `(Dec)Interval::div` and `(Dec)Interval::mul_rev_to_pair`, so it has to be updated
        // along with it.
        // P / N0 => [-∞, a/c] = [+∞; a/c] = [+∞; -a/-c]
        let x = self.rep; // [-a; b]
        let y = rhs.rep; // [-c; d]
        Self {
            rep: shuffle02(splat(f64::INFINITY), div_ru(x, y)),
        }
    }

    #[inline]
    pub(crate) fn div_p_n1(self, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proofs of
        // `(Dec)Interval::div` and `(Dec)Interval::mul_rev_to_pair`, so it has to be updated
        // along with it.
        // P / N1 => [b/d, a/c] = [-b/d; a/c] = [-b/d; -a/-c] = [-b; -a] ./ [d; -c]
        let x = swap(self.rep); // [b; -a]
        let x = neg0(x); // [-b; -a]
        let y = swap(rhs.rep); // [d; -c]
        Self { rep: div_ru(x, y) }
    }

    #[inline]
    pub(crate) fn div_p_p0(self, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proofs of
        // `(Dec)Interval::div` and `(Dec)Interval::mul_rev_to_pair`, so it has to be updated
        // along with it.
        // P / P0 => [a/d, +∞] = [-a/d; +∞]
        let x = self.rep; // [-a; b]
        let y = swap(rhs.rep); // [d; -c]
        Self {
            rep: shuffle02(div_ru(x, y), splat(f64::INFINITY)),
        }
    }

    #[inline]
    pub(crate) fn div_p_p1(self, rhs: Self) -> Self {
        // `rocq/theories/Model.v` transcribes this function for the proofs of
        // `(Dec)Interval::div` and `(Dec)Interval::mul_rev_to_pair`, so it has to be updated
        // along with it.
        // P / P1 => [a/d, b/c] = [-a/d; b/c] = [-a; b] ./ [d; c]
        let x = self.rep; // [-a; b]
        let y = neg0(rhs.rep); // [c; d]
        let y = swap(y); // [d; c]
        Self { rep: div_ru(x, y) }
    }

    /// Returns the reverse multiplication $\numerator \setdiv′ \self$
    /// (beware the order of the arguments) as an array of two intervals.
    /// The operation is also known as *two-output division* in IEEE Std 1788-2015.
    ///
    /// For intervals $𝒙$ and $𝒚$, the reverse multiplication is defined as:
    ///
    /// $$
    /// 𝒙 \setdiv′ 𝒚 = \set{z ∈ \R ∣ ∃y ∈ 𝒚 : zy ∈ 𝒙}.
    /// $$
    ///
    /// For comparison, the standard division is defined as:
    ///
    /// $$
    /// \begin{align*}
    ///  𝒙 \setdiv 𝒚 &= \set{x / y ∣ (x, y) ∈ 𝒙 × 𝒚 ∖ \set 0} \\\\
    ///   &= \set{z ∈ \R ∣ ∃y ∈ 𝒚 ∖ \set 0 : zy ∈ 𝒙}.
    /// \end{align*}
    /// $$
    ///
    /// The interval division $𝒙 / 𝒚$ is an enclosure of $𝒙 \setdiv 𝒚$.
    /// A notable difference between two definitions is that when $𝒙 = 𝒚 = \set 0$,
    /// $𝒙 \setdiv 𝒚 = ∅$, while $𝒙 \setdiv′ 𝒚 = \R$.
    ///
    /// The function returns:
    ///
    /// - `[`[`Interval::EMPTY`]`; 2]` if $\numerator \setdiv′ \self$ is empty;
    /// - `[z, `[`Interval::EMPTY`]`]` if $\numerator \setdiv′ \self$ has one component $𝒛$,
    ///   where `z` is the tightest enclosure of $𝒛$;
    /// - `[z1, z2]` if $\numerator \setdiv′ \self$ has two components $𝒛₁$ and $𝒛₂$
    ///   ordered so that $\sup 𝒛₁ ≤ \inf 𝒛₂$,
    ///   where `z1` and `z2` are the tightest enclosures of $𝒛₁$ and $𝒛₂$, respectively.
    ///
    /// When $\self ≠ ∅ ∧ \numerator ≠ ∅$, the number of components $\numerator \setdiv′ \self$ has
    /// are summarized as:
    ///
    /// |             | $0 ∈ \numerator$ | $0 ∉ \numerator$ |
    /// | :---------: | :--------------: | :--------------: |
    /// | $0 ∈ \self$ |        1         |    0, 1, or 2    |
    /// | $0 ∉ \self$ |        1         |        1         |
    ///
    /// # Examples
    ///
    /// ```
    /// use inari::{Interval as I, const_interval as c};
    /// let zero = c!(0.0, 0.0);
    /// assert_eq!(zero.mul_rev_to_pair(c!(1.0, 2.0)), [I::EMPTY; 2]);
    /// assert_eq!(zero.mul_rev_to_pair(c!(0.0, 2.0)), [I::ENTIRE, I::EMPTY]);
    /// assert_eq!(zero.mul_rev_to_pair(zero), [I::ENTIRE, I::EMPTY]);
    /// let x = c!(1.0, 2.0);
    /// assert_eq!(I::ENTIRE.mul_rev_to_pair(x), [c!(f64::NEG_INFINITY, 0.0), c!(0.0, f64::INFINITY)]);
    /// assert_eq!(c!(1.0, 1.0).mul_rev_to_pair(x), [x, I::EMPTY]);
    /// assert_eq!(c!(1.0, f64::INFINITY).mul_rev_to_pair(c!(1.0, 1.0)),
    ///            [c!(0.0, 1.0), I::EMPTY]);
    /// assert_eq!(c!(-1.0, 1.0).mul_rev_to_pair(c!(1.0, 2.0)),
    ///            [c!(f64::NEG_INFINITY, -1.0), c!(1.0, f64::INFINITY)]);
    /// assert_eq!(c!(-1.0, 1.0).mul_rev_to_pair(zero), [I::ENTIRE, I::EMPTY]);
    /// ```
    #[must_use]
    pub fn mul_rev_to_pair(self, numerator: Self) -> [Self; 2] {
        // Proved correct in `rocq/theories/MulRev.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        use IntervalClass2::*;
        match numerator.classify2(self) {
            E_E | E_M | E_N0 | E_N1 | E_P0 | E_P1 | E_Z | M_E | N0_E | N1_E | N1_Z | P0_E
            | P1_E | P1_Z | Z_E => [Self::EMPTY; 2],
            M_Z | N0_Z | P0_Z | Z_Z | M_M | M_N0 | M_P0 | N0_M | P0_M | Z_M | Z_N0 | Z_P0
            | N0_N0 | N0_P0 | P0_N0 | P0_P0 => [Self::ENTIRE, Self::EMPTY],
            Z_N1 | Z_P1 => [Self::zero(), Self::EMPTY],
            N1_M => {
                // N1 / M => [-∞, b/d] ∪ [b/c, +∞] = [+∞; b/d] ∪ [-b/c; +∞]
                // [-b/c, b/d] = [b; b] ./ [-c; d]
                let x = numerator.rep; // [-a; b]
                let x = shuffle13(x, x); // [b; b]
                let q = div_ru(x, self.rep); // [b/(-c); b/d]
                [
                    Self {
                        rep: shuffle13(splat(f64::INFINITY), q),
                    },
                    Self {
                        rep: shuffle02(q, splat(f64::INFINITY)),
                    },
                ]
            }
            P1_M => {
                // P1 / M => [-∞, a/c] ∪ [a/d, +∞] = [+∞; a/c] ∪ [-a/d; +∞]
                // [a/c; -a/d] = [-a; -a] ./ [-c; d]
                let x = numerator.rep; // [-a; b]
                let x = shuffle02(x, x); // [-a; -a]
                let q = div_ru(x, self.rep); // [a/c; -a/d]
                [
                    Self {
                        rep: shuffle02(splat(f64::INFINITY), q),
                    },
                    Self {
                        rep: shuffle13(q, splat(f64::INFINITY)),
                    },
                ]
            }
            M_N1 => [numerator.div_m_n1(self), Self::EMPTY],
            M_P1 => [numerator.div_m_p1(self), Self::EMPTY],
            N1_N0 => [numerator.div_n_n0(self), Self::EMPTY],
            N0_N1 | N1_N1 => [numerator.div_n_n1(self), Self::EMPTY],
            N1_P0 => [numerator.div_n_p0(self), Self::EMPTY],
            N0_P1 | N1_P1 => [numerator.div_n_p1(self), Self::EMPTY],
            P1_N0 => [numerator.div_p_n0(self), Self::EMPTY],
            P0_N1 | P1_N1 => [numerator.div_p_n1(self), Self::EMPTY],
            P1_P0 => [numerator.div_p_p0(self), Self::EMPTY],
            P0_P1 | P1_P1 => [numerator.div_p_p1(self), Self::EMPTY],
        }
    }

    /// Returns the tightest interval `z` such that `rhs` $+$ `z` $⊇$ `self`,
    /// if both `self` and `rhs` are bounded and the width of `self` is greater than or equal to
    /// that of `rhs`. Otherwise, returns [`Interval::ENTIRE`].
    ///
    /// Even when `x.cancel_minus(y)` is not [`Interval::ENTIRE`], its value is generally
    /// different from `x - y`, as the latter gives the tightest enclosure of `x` $-$ `y`,
    /// while the former does not always enclose `x` $-$ `y`.
    /// In such case, `x.cancel_minus(y)` $⊆$ `x - y` holds, but generally not the equality.
    ///
    /// # Examples
    ///
    /// Getting an enclosure of a partial sum omitting a single term from their total:
    ///
    /// ```
    /// use inari::*;
    /// let x = interval!("[0.1, 0.2]").unwrap();
    /// let y = interval!("[0.3, 0.4]").unwrap();
    /// let z = interval!("[0.5, 0.6]").unwrap();
    /// let sum = x + y + z;
    /// assert!((y + z).subset(sum.cancel_minus(x)));
    /// assert!((x + z).subset(sum.cancel_minus(y)));
    /// assert!((x + y).subset(sum.cancel_minus(z)));
    /// ```
    ///
    /// `sum.cancel_minus(x)` is a subset of `sum - x`:
    ///
    /// ```
    /// # use inari::*;
    /// # let x = interval!("[0.1, 0.2]").unwrap();
    /// # let y = interval!("[0.3, 0.4]").unwrap();
    /// # let z = interval!("[0.5, 0.6]").unwrap();
    /// # let sum = x + y + z;
    /// assert!(sum.cancel_minus(x).subset(sum - x));
    /// ```
    ///
    /// But the inverse does not hold in general:
    ///
    /// ```should_panic
    /// # use inari::*;
    /// # let x = interval!("[0.1, 0.2]").unwrap();
    /// # let y = interval!("[0.3, 0.4]").unwrap();
    /// # let z = interval!("[0.5, 0.6]").unwrap();
    /// # let sum = x + y + z;
    /// assert!((sum - x).subset(sum.cancel_minus(x)));
    /// ```
    ///
    /// `sum.cancel_minus(x)`, etc. returns [`Interval::ENTIRE`] when `sum` is unbounded:
    ///
    /// ```
    /// use inari::*;
    /// let x = const_interval!(1.0, 2.0);
    /// let y = const_interval!(3.0, f64::MAX);
    /// let sum = x + y;
    /// assert_eq!(sum.cancel_minus(x), Interval::ENTIRE);
    /// assert_eq!(sum.cancel_minus(y), Interval::ENTIRE);
    /// ```
    ///
    /// `sum.cancel_minus(x)` returns [`Interval::ENTIRE`] when the width of “`sum`” is
    /// less than that of `x`:
    ///
    /// ```
    /// use inari::*;
    /// let x = const_interval!(1.0, 2.0);
    /// let sum = const_interval!(4.0, 4.5);
    /// assert_eq!(sum.cancel_minus(x), Interval::ENTIRE);
    /// ```
    #[must_use]
    pub fn cancel_minus(self, rhs: Self) -> Self {
        use Ordering::*;
        // cancel_minus([a, b], [c, d]) =
        //
        //            | Empty  | Common | Unbounded
        // -----------+--------+--------+-----------
        //  Empty     | Empty  | Empty  |  Entire
        //  Common    | Entire |   *1   |  Entire
        //  Unbounded | Entire | Entire |  Entire
        //
        // *1  | [a - c, b - d]  if width(x) ≥ width(y),
        //     | Entire          otherwise.
        if self.is_empty() && (rhs.is_empty() || rhs.is_common_interval()) {
            return Self::EMPTY;
        }
        if !self.is_common_interval() || rhs.is_empty() || !rhs.is_common_interval() {
            return Self::ENTIRE;
        }

        let x = self.rep; // [-a; b]
        let y = rhs.rep; // [-c; d]
        let z = sub_ru(x, y); // [a - c, b - d] = [c - a; b - d] = [-a; b] .- [-c; d]
        let w_rn = hadd_rn(x, y); // [width(x); width(y)] = [b - a; d - c] = [-a; -c] .+ [b; d],
                                  // rounded to nearest, ≥ 0.
        let [wx, wy] = extract(w_rn);
        let (x, y, w_rn) = if wx == f64::INFINITY && wy == f64::INFINITY {
            // Both widths overflow, so every bound is at least 2^970 in magnitude:
            // b - a ≥ 2^1024 - 2^970 and b ≤ f64::MAX = 2^1024 - 2^971 give -a ≥ 2^970,
            // and the same holds for b, c and d. Halving such a float is exact, and the
            // halved widths are at most f64::MAX, so they are compared instead.
            let [ma, b] = extract(x);
            let [mc, d] = extract(y);
            let x = constant(0.5 * ma, 0.5 * b);
            let y = constant(0.5 * mc, 0.5 * d);
            (x, y, hadd_rn(x, y))
        } else {
            (x, y, w_rn)
        };
        let [wx, wy] = extract(w_rn);
        // `wx` and `wy` are not NaN as `x` and `y` are common intervals.
        match wx.partial_cmp(&wy) {
            Some(Greater) => {
                // width(x) > width(y) without rounding.
                // `z.inf()` cannot be +∞ due to rounding downward.
                Self { rep: z }
            }
            Some(Less) => Self::ENTIRE,
            Some(Equal) => {
                // wx = wy < +∞.
                // Use the Fast2Sum algorithm (T. J. Dekker, A floating-point technique for
                // extending the available precision, Numer. Math. 18, 1971) to compute the
                // remainders dx and dy, where
                //   -a + b = wx + dx, -c + d = wy + dy, or
                //   [-a; -c] .+ [b; d] = w_rn .+ dw.
                // It needs an addend whose magnitude is at least that of the other:
                // -a + b ≥ 0, so the larger of -a and b is at least |the smaller|, and the
                // same holds for -c and d. No step overflows, unlike in 2Sum, which
                // overflows for x = y = [f64::MIN, -3 × 2^970].
                //
                // (w_rn, dw) = elementwise_fast_two_sum(hi, lo)
                //   hi := max([-a; -c], [b; d]), lo := min([-a; -c], [b; d])
                //   w_rn = hi .+ lo
                //   t := hi .- w_rn
                //   dw := lo .+ t
                let hi = max(shuffle02(x, y), shuffle13(x, y));
                let lo = min(shuffle02(x, y), shuffle13(x, y));
                let t = sub_rn(hi, w_rn);
                let dw = add_rn(lo, t);
                let [dwx, dwy] = extract(dw);
                if dwx >= dwy {
                    Self { rep: z }
                } else {
                    Self::ENTIRE
                }
            }
            None => unreachable!(),
        }
    }

    /// `x.cancel_plus(y)` is equivalent to `x.cancel_minus(-y)`.
    ///
    /// See [`Interval::cancel_minus`] for more information.
    #[inline]
    #[must_use]
    pub fn cancel_plus(self, rhs: Self) -> Self {
        self.cancel_minus(-rhs)
    }

    /// Returns $(\self × \rhs) + \addend$.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain | Range |
    /// | ------ | ----- |
    /// | $\R^3$ | $\R$  |
    // Almost a copy-paste of mul. Additions/modifications are indicated with "// *".
    #[allow(clippy::many_single_char_names)]
    #[must_use]
    pub fn mul_add(self, rhs: Self, addend: Self) -> Self {
        if addend.is_empty() {
            return Self::EMPTY; // *
        }

        use IntervalClass2::*;
        match self.classify2(rhs) {
            E_E | E_M | E_N0 | E_N1 | E_P0 | E_P1 | E_Z | M_E | N0_E | N1_E | P0_E | P1_E | Z_E => {
                Self::EMPTY
            }
            M_Z | N0_Z | N1_Z | P0_Z | P1_Z | Z_M | Z_N0 | Z_N1 | Z_P0 | Z_P1 | Z_Z => addend, // *
            M_M => {
                let x = shuffle02(self.rep, self.rep);
                let y = swap(rhs.rep);
                let xy = mul_add_ru(x, y, addend.rep); // *
                let z = shuffle13(self.rep, self.rep);
                let w = rhs.rep;
                let zw = mul_add_ru(z, w, addend.rep); // *
                let r = max(xy, zw);
                Self { rep: r }
            }
            M_N0 | M_N1 => {
                let x = swap(self.rep);
                let y = shuffle02(rhs.rep, rhs.rep);
                Self {
                    rep: mul_add_ru(x, y, addend.rep), // *
                }
            }
            M_P0 | M_P1 => {
                let x = self.rep;
                let y = shuffle13(rhs.rep, rhs.rep);
                Self {
                    rep: mul_add_ru(x, y, addend.rep), // *
                }
            }
            N0_M | N1_M => {
                let x = shuffle02(self.rep, self.rep);
                let y = swap(rhs.rep);
                Self {
                    rep: mul_add_ru(x, y, addend.rep), // *
                }
            }
            N0_N0 | N0_N1 | N1_N0 | N1_N1 => {
                let x = swap(self.rep);
                let x = neg0(x);
                let y = swap(rhs.rep);
                Self {
                    rep: mul_add_ru(x, y, addend.rep), // *
                }
            }
            N0_P0 | N0_P1 | N1_P0 | N1_P1 => {
                let x = self.rep;
                let y = neg0(rhs.rep);
                let y = swap(y);
                Self {
                    rep: mul_add_ru(x, y, addend.rep), // *
                }
            }
            P0_M | P1_M => {
                let x = shuffle13(self.rep, self.rep);
                let y = rhs.rep;
                Self {
                    rep: mul_add_ru(x, y, addend.rep), // *
                }
            }
            P0_N0 | P0_N1 | P1_N0 | P1_N1 => {
                let x = neg0(self.rep);
                let x = swap(x);
                let y = rhs.rep;
                Self {
                    rep: mul_add_ru(x, y, addend.rep), // *
                }
            }
            P0_P0 | P0_P1 | P1_P0 | P1_P1 => {
                let x = self.rep;
                let y = neg0(rhs.rep);
                Self {
                    rep: mul_add_ru(x, y, addend.rep), // *
                }
            }
        }
    }

    /// Returns the multiplicative inverse of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain        | Range         |
    /// | ------------- | ------------- |
    /// | $\R ∖ \set 0$ | $\R ∖ \set 0$ |
    #[must_use]
    pub fn recip(self) -> Self {
        // Proved correct in `rocq/theories/Recip.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        use IntervalClass::*;
        match self.classify() {
            E | Z => Self::EMPTY,
            M => Self::ENTIRE,
            N0 => {
                // 1 / N0 => [-∞, 1/a] = [+∞; -1/-a]
                let x = splat(-1.0);
                let y = self.rep; // [-a; b]
                Self {
                    rep: shuffle02(splat(f64::INFINITY), div_ru(x, y)),
                }
            }
            N1 => {
                // 1 / N1 => [1/b, 1/a] = [-1/b; 1/a] = [-1/b; -1/-a] = [-1; -1] ./ [b; -a]
                let x = splat(-1.0);
                let y = swap(self.rep); // [b; -a]
                Self { rep: div_ru(x, y) }
            }
            P0 => {
                // 1 / P0 => [1/b, +∞] = [-1/b; +∞]
                let x = splat(-1.0);
                let y = self.rep; // [-a; b]
                Self {
                    rep: shuffle13(div_ru(x, y), splat(f64::INFINITY)),
                }
            }
            P1 => {
                // 1 / P1 => [1/b, 1/a] = [-1/b; 1/a] = [-1/b; -1/-a] = [-1; -1] ./ [b; -a]
                let x = splat(-1.0);
                let y = swap(self.rep); // [b; -a]
                Self { rep: div_ru(x, y) }
            }
        }
    }

    /// Returns the square of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain | Range     |
    /// | ------ | --------- |
    /// | $\R$   | $\[0, ∞)$ |
    #[must_use]
    pub fn sqr(self) -> Self {
        // Proved correct in `rocq/theories/Sqr.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        use IntervalClass::*;
        match self.classify() {
            E => Self::EMPTY,
            Z => Self::zero(),
            M => {
                // [0, max(a^2, b^2)] = [0; max(a^2, b^2)]
                let x = self.rep; // [-a; b]
                let r = mul_ru(x, x); // [a^2; b^2]
                let r = max(r, swap(r)); // [max(a^2, b^2); _]
                Self {
                    rep: shuffle02(splat(0.0), r),
                }
            }
            N0 | N1 => {
                // [b^2, a^2] = [-b^2; a^2] = [-b; -a] .* [b; -a]
                let x = swap(self.rep); // [b; -a]
                let y = neg0(x); // [-b; -a]
                Self { rep: mul_ru(x, y) }
            }
            P0 | P1 => {
                // [a^2, b^2] = [-a^2; b^2] = [-a; b] .* [a; b]
                let x = self.rep; // [-a; b]
                let y = neg0(x); // [a; b]
                Self { rep: mul_ru(x, y) }
            }
        }
    }

    /// Returns the principal square root of `self`.
    ///
    /// The domain and the range of the point function are:
    ///
    /// | Domain    | Range     |
    /// | --------- | --------- |
    /// | $\[0, ∞)$ | $\[0, ∞)$ |
    #[must_use]
    pub fn sqrt(self) -> Self {
        // Proved correct in `rocq/theories/Sqrt.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        if self.is_empty() {
            return Self::EMPTY;
        }

        let a = self.inf_raw();
        let b = self.sup_raw();

        if b < 0.0 {
            Self::EMPTY
        } else if a <= 0.0 {
            // Only one square root is needed, so `sqrt_rd_ru` would be wasted: a
            // lower lane of zero fails its fast-path check (see BENCHMARKS.md).
            Self::with_infsup_raw(0.0, sqrt1_ru(b))
        } else {
            // Both endpoints in one vector square root. `neg0` turns the
            // representation [-a; b] into [a; b], and back afterward.
            Self {
                rep: neg0(sqrt_rd_ru(neg0(self.rep))),
            }
        }
    }
}

impl DecInterval {
    /// The decorated version of [`Interval::mul_rev_to_pair`].
    ///
    /// `[`[`DecInterval::NAI`]`; 2]` is returned if `self` or `numerator` is NaI.
    /// When $0 ∉ \self ≠ ∅ ∧ \numerator ≠ ∅$, `[z,`[`DecInterval::EMPTY`]`]` is returned
    /// with `z` being the same as `numerator / self` and decorated the same way.
    /// In all other cases, both outputs are decorated with [`Decoration::Trv`].
    #[must_use]
    pub fn mul_rev_to_pair(self, numerator: Self) -> [Self; 2] {
        // Proved correct in `rocq/theories/MulRev.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        if self.is_nai() || numerator.is_nai() {
            return [Self::NAI; 2];
        }
        let [u, v] = self.x.mul_rev_to_pair(numerator.x);
        let d = if self.x.contains(0.0) {
            Decoration::Trv
        } else {
            self.d.min(numerator.d)
        };
        [Self::set_dec(u, d), Self::set_dec(v, Decoration::Trv)]
    }

    /// The decorated version of [`Interval::cancel_minus`].
    ///
    /// A NaI is returned if `self` or `rhs` is NaI.
    #[must_use]
    pub fn cancel_minus(self, rhs: Self) -> Self {
        if self.is_nai() || rhs.is_nai() {
            return Self::NAI;
        }
        Self::set_dec(self.x.cancel_minus(rhs.x), Decoration::Trv)
    }

    /// The decorated version of [`Interval::cancel_plus`].
    ///
    /// A NaI is returned if `self` or `rhs` is NaI.
    #[must_use]
    pub fn cancel_plus(self, rhs: Self) -> Self {
        if self.is_nai() || rhs.is_nai() {
            return Self::NAI;
        }
        Self::set_dec(self.x.cancel_plus(rhs.x), Decoration::Trv)
    }

    /// The decorated version of [`Interval::mul_add`].
    ///
    /// A NaI is returned if `self`, `rhs` or `addend` is NaI.
    #[must_use]
    pub fn mul_add(self, rhs: Self, addend: Self) -> Self {
        if self.is_nai() || rhs.is_nai() || addend.is_nai() {
            return Self::NAI;
        }

        Self::set_dec(
            self.x.mul_add(rhs.x, addend.x),
            self.d.min(rhs.d.min(addend.d)),
        )
    }

    /// The decorated version of [`Interval::recip`].
    ///
    /// A NaI is returned if `self` is NaI.
    #[must_use]
    pub fn recip(self) -> Self {
        // Proved correct in `rocq/theories/Recip.v` for the portable backend if `self` is
        // `com` only when `self.x` is common, which `rocq/theories/ComCommon.v` proves of
        // every `DecInterval` that the library makes.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        if self.is_nai() {
            return self;
        }

        let d = if self.x.contains(0.0) {
            Decoration::Trv
        } else {
            self.d
        };
        Self::set_dec(self.x.recip(), d)
    }

    /// The decorated version of [`Interval::sqr`].
    ///
    /// A NaI is returned if `self` is NaI.
    #[must_use]
    pub fn sqr(self) -> Self {
        // Proved correct in `rocq/theories/Sqr.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        if self.is_nai() {
            return self;
        }

        Self::set_dec(self.x.sqr(), self.d)
    }

    /// The decorated version of [`Interval::sqrt`].
    ///
    /// A NaI is returned if `self` is NaI.
    #[must_use]
    pub fn sqrt(self) -> Self {
        // Proved correct in `rocq/theories/Sqrt.v` for the portable backend.
        // `rocq/theories/Model.v` transcribes this function, so it has to be updated
        // along with it.
        if self.is_nai() {
            return self;
        }

        let d = if self.x.inf_raw() < 0.0 {
            Decoration::Trv
        } else {
            self.d
        };
        Self::set_dec(self.x.sqrt(), d)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use DecInterval as DI;
    use Interval as I;

    #[test]
    fn empty() {
        assert!((I::EMPTY.mul_add(I::PI, I::PI)).is_empty());
        assert!((I::PI.mul_add(I::EMPTY, I::PI)).is_empty());
        assert!((I::PI.mul_add(I::PI, I::EMPTY)).is_empty());

        assert!(I::EMPTY.recip().is_empty());
        assert!(I::EMPTY.sqrt().is_empty());
        assert!(I::EMPTY.sqr().is_empty());

        assert!((DI::EMPTY.mul_add(DI::PI, DI::PI)).is_empty());
        assert!((DI::PI.mul_add(DI::EMPTY, DI::PI)).is_empty());
        assert!((DI::PI.mul_add(DI::PI, DI::EMPTY)).is_empty());

        assert!(DI::EMPTY.recip().is_empty());
        assert!(DI::EMPTY.sqrt().is_empty());
        assert!(DI::EMPTY.sqr().is_empty());
    }

    #[test]
    fn nai() {
        assert!((DI::NAI.mul_add(DI::PI, DI::PI)).is_nai());
        assert!((DI::PI.mul_add(DI::NAI, DI::PI)).is_nai());
        assert!((DI::PI.mul_add(DI::PI, DI::NAI)).is_nai());

        assert!(DI::NAI.recip().is_nai());
        assert!(DI::NAI.sqrt().is_nai());
        assert!(DI::NAI.sqr().is_nai());
    }

    #[test]
    fn mul_rev_to_pair() {
        let zero = const_interval!(0., 0.);
        assert_eq!(zero.mul_rev_to_pair(const_interval!(1., 2.)), [I::EMPTY; 2]);
        let pos = const_interval!(0., f64::INFINITY);
        let neg = const_interval!(f64::NEG_INFINITY, 0.);
        assert_eq!(
            I::ENTIRE.mul_rev_to_pair(const_interval!(1., 1.)),
            [neg, pos]
        );
        assert_eq!(pos.mul_rev_to_pair(pos), [I::ENTIRE, I::EMPTY]);
        assert_eq!(neg.mul_rev_to_pair(pos), [I::ENTIRE, I::EMPTY]);
    }

    #[test]
    fn cancel_minus() {
        assert_eq!(
            const_interval!(f64::MAX, f64::MAX).cancel_minus(const_interval!(f64::MIN, f64::MIN)),
            const_interval!(f64::MAX, f64::INFINITY)
        );
        assert_eq!(
            const_interval!(f64::MIN, f64::MIN).cancel_minus(const_interval!(f64::MAX, f64::MAX)),
            const_interval!(f64::NEG_INFINITY, f64::MIN)
        );
        assert_eq!(
            const_interval!(1e292, f64::MAX).cancel_minus(const_interval!(f64::MIN, f64::MIN)),
            const_interval!(f64::MAX, f64::INFINITY)
        );
        assert_eq!(
            const_interval!(f64::MAX, f64::MAX).cancel_minus(const_interval!(f64::MIN, -1e292)),
            I::ENTIRE
        );

        // 2^970, half an ulp of `f64::MAX`. Computing the remainders of the widths with
        // 2Sum instead of Fast2Sum overflowed here, which gave `Interval::ENTIRE`.
        let h = f64::from_bits((970 + 1023) << 52);
        let x = I::try_from((f64::MIN, -3.0 * h)).unwrap();
        assert_eq!(x.cancel_minus(x), const_interval!(0.0, 0.0));
        // The widths overflow and are equal, and a - c = b - d = -(2^1024 - 5 × 2^970).
        let x = I::try_from((f64::MIN, h)).unwrap();
        let y = I::try_from((-3.0 * h, f64::MAX - 2.0 * h)).unwrap();
        assert_eq!(
            x.cancel_minus(y),
            I::try_from((f64::MIN + 2.0 * h, f64::MIN + 4.0 * h)).unwrap()
        );
        assert_eq!(
            x.cancel_plus(-y),
            I::try_from((f64::MIN + 2.0 * h, f64::MIN + 4.0 * h)).unwrap()
        );
    }
}
