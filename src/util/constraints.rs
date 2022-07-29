use std::{
    fmt::{Debug, Display},
    ops::Add,
};

use self::{
    bound_constants::INFINITY,
    bound_strictness::*,
    inner_raw_constants::{INNER_LE_OVERFLOW, INNER_LE_ZERO, INNER_LS_INFINITY},
};

use derive_more::{Add, Neg, Sub};

pub type ClockIndex = usize;
pub type Bound = i32;
pub(crate) type InnerRawInequality = i32;

mod bound_strictness {
    use super::InnerRawInequality;

    pub const STRICT: InnerRawInequality = 0;
    pub const WEAK: InnerRawInequality = 1;
}

/*
pub struct Constraint {
    inequality: RawInequality,
    i: ClockIndex,
    j: ClockIndex,
}

impl Constraint {
    pub fn new(i: ClockIndex, j: ClockIndex, inequality: Inequality) -> Self {
        Self {
            inequality: inequality.into(),
            i,
            j,
        }
    }
}*/

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Add, Sub, Neg)]
pub struct RawInequality {
    inner: InnerRawInequality,
}

pub enum Strictness {
    Strict,
    Weak,
}

impl RawInequality {
    pub const MAX: Self = Self {
        inner: InnerRawInequality::MAX,
    };

    pub const MIN: Self = Self {
        inner: InnerRawInequality::MIN,
    };

    pub const ZERO: Self = Self { inner: 0 };

    pub const fn from_inequality(ineq: &Inequality) -> Self {
        let inner = match *ineq {
            Inequality::LS(bound) => (bound * 2) | STRICT,
            Inequality::LE(bound) => (bound * 2) | WEAK,
        };
        Self { inner }
    }

    pub const fn is_strict(&self) -> bool {
        let is_strict = self.inner & 1 == 0;
        is_strict
    }

    pub const fn bound(&self) -> Bound {
        self.inner >> 1
    }

    pub fn is_inf(&self) -> bool {
        self.inner == INNER_LS_INFINITY
    }

    pub fn is_zero(&self) -> bool {
        self.inner == INNER_LE_ZERO
    }

    pub fn as_weak(&self) -> Self {
        assert!(!self.is_inf());
        Self {
            inner: self.inner | WEAK,
        }
    }

    pub fn add_raw(self, rhs: Self) -> Self {
        let x = self.inner;
        let y = rhs.inner;
        assert!(x <= INNER_LS_INFINITY);
        assert!(y <= INNER_LS_INFINITY);
        assert!(self.is_valid());
        assert!(rhs.is_valid());
        if x == INNER_LS_INFINITY || y == INNER_LS_INFINITY {
            INNER_LS_INFINITY.into()
        } else {
            ((x + y) - ((x | y) & 1)).into()
        }
    }

    pub fn as_strict(&self) -> Self {
        // TODO: maybe we need this check, UPPAAL does not do it
        // assert!(!self.is_zero());
        Self {
            inner: self.inner & !WEAK,
        }
    }

    pub fn as_negated_strictness(&self) -> Self {
        Self {
            inner: self.inner ^ WEAK,
        }
    }

    pub fn with_increment(&self, increment: i32) -> Self {
        let inner = self.inner;
        if inner < INNER_LS_INFINITY {
            (inner + increment).into()
        } else {
            *self
        }
    }

    pub fn with_decrement(&self, decrement: i32) -> Self {
        let inner = self.inner;
        if inner < INNER_LS_INFINITY {
            (inner - decrement).into()
        } else {
            *self
        }
    }

    /// Negate an inequality:
    ///
    /// neg(<a) = <=-a
    ///
    /// neg(<=a) = <-a
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// # use edbm::util::constraints::{RawInequality, Inequality::*};
    /// let raw1: RawInequality = LE(-2).into();
    /// let raw2: RawInequality = LS(2).into();
    /// let neg_raw1 = raw1.as_negated();
    /// let neg_raw2 = raw2.as_negated();
    /// assert!(raw1 == neg_raw2);
    /// assert!(neg_raw1 == raw2);
    /// ```
    pub fn as_negated(&self) -> Self {
        Self {
            inner: 1 - self.inner,
        }
    }

    /// Negate a weak inequality:
    ///
    /// neg(<=a) = <=-a
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// # use edbm::util::constraints::{RawInequality, Inequality::*};
    /// let raw1: RawInequality = LE(-2).into();
    /// let raw2: RawInequality = LE(2).into();
    /// let neg_raw1 = raw1.as_negated_weak();
    /// let neg_raw2 = raw2.as_negated_weak();
    /// assert!(raw1 == neg_raw2);
    /// assert!(neg_raw1 == raw2);
    /// ```
    pub fn as_negated_weak(&self) -> Self {
        assert!(!self.is_strict());
        Self {
            inner: 2 - self.inner,
        }
    }

    /// Returns true if adding this constraint to any constraint does not overflow.
    pub fn is_valid(&self) -> bool {
        let inner = self.inner;
        inner == INNER_LS_INFINITY || (inner < INNER_LE_OVERFLOW && -inner < INNER_LE_OVERFLOW)
    }
}
/*
impl Add for RawInequality {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let x = self.inner;
        let y = rhs.inner;
        assert!(x <= INNER_LS_INFINITY);
        assert!(y <= INNER_LS_INFINITY);
        assert!(self.is_valid());
        assert!(rhs.is_valid());
        if x == INNER_LS_INFINITY || y == INNER_LS_INFINITY {
            INNER_LS_INFINITY.into()
        } else {
            ((x + y) - ((x | y) & 1)).into()
        }
    }
}*/

impl Display for RawInequality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ineq: Inequality = (*self).into();
        f.write_fmt(format_args!("{}", ineq))
    }
}

impl Debug for RawInequality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args! {"raw{{{}}}", self.inner})
    }
}

impl Into<Inequality> for RawInequality {
    fn into(self) -> Inequality {
        let bound = self.bound();
        if self.is_strict() {
            Inequality::LS(bound)
        } else {
            Inequality::LE(bound)
        }
    }
}

impl From<Inequality> for RawInequality {
    fn from(ineq: Inequality) -> Self {
        RawInequality::from_inequality(&ineq)
    }
}

impl From<InnerRawInequality> for RawInequality {
    fn from(inner: InnerRawInequality) -> Self {
        Self { inner }
    }
}

pub mod bound_constants {
    use super::Bound;

    pub const INFINITY: Bound = Bound::MAX >> 1;
    pub(crate) const OVERFLOW: Bound = Bound::MAX >> 2;
}

mod inner_raw_constants {
    use super::Inequality::{self, *};
    use super::InnerRawInequality;
    use super::{
        bound_constants::{INFINITY, OVERFLOW},
        RawInequality,
    };

    const fn as_inner(l: Inequality) -> InnerRawInequality {
        RawInequality::from_inequality(&l).inner
    }

    pub const INNER_LE_ZERO: InnerRawInequality = as_inner(LE(0));
    pub const INNER_LS_INFINITY: InnerRawInequality = as_inner(LS(INFINITY));
    pub(crate) const INNER_LE_OVERFLOW: InnerRawInequality = as_inner(LE(OVERFLOW));
}

pub mod raw_constants {
    use super::Inequality::{self, *};
    use super::{bound_constants::INFINITY, RawInequality};

    const fn as_raw(l: Inequality) -> RawInequality {
        RawInequality::from_inequality(&l)
    }

    pub const ZERO: RawInequality = RawInequality::ZERO;
    pub const LE_ZERO: RawInequality = as_raw(LE(0));
    pub const LS_INFINITY: RawInequality = as_raw(LS(INFINITY));
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Inequality {
    LS(Bound),
    LE(Bound),
}
impl Inequality {
    pub fn bound(&self) -> Bound {
        match self {
            Inequality::LS(bound) | Inequality::LE(bound) => *bound,
        }
    }

    pub fn is_inf(&self) -> bool {
        *self == Self::LS(INFINITY)
    }
}

impl Display for Inequality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_inf() {
            f.write_str("<∞")
        } else {
            match self {
                Inequality::LS(bound) => f.write_fmt(format_args!("<{}", bound)),
                Inequality::LE(bound) => f.write_fmt(format_args!("≤{}", bound)),
            }
        }
    }
}

impl Add for Inequality {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let raw1: RawInequality = self.into();
        let raw2: RawInequality = rhs.into();

        (raw1.add_raw(raw2)).into()
    }
}
