use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    ops::Add,
};

use self::{
    bound_constants::INFINITY,
    bound_strictness::*,
    inner_raw_constants::{INNER_LE_OVERFLOW, INNER_LE_ZERO, INNER_LS_INFINITY},
    raw_constants::{LE_ZERO, LS_INFINITY},
};

use derive_more::{Add, AddAssign, BitAnd, Neg, Sub, SubAssign};

pub type ClockIndex = usize;
pub type Bound = i32;
pub(crate) type InnerRawInequality = i32;

// Based on the UDBM implementation
mod bound_strictness {
    use super::InnerRawInequality;

    pub const STRICT: InnerRawInequality = 0;
    pub const WEAK: InnerRawInequality = 1;
}

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Add, Sub, Neg, Hash, AddAssign, SubAssign, BitAnd,
)]
pub struct RawInequality {
    inner: InnerRawInequality,
}

pub enum Strictness {
    Strict,
    Weak,
}

// Based on the UDBM implementation of raw_t and helper functions
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
        self.inner & 1 == 0
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

    pub fn raw_inc(self, rhs: Self) -> Self {
        if self < LS_INFINITY {
            self + rhs
        } else {
            LS_INFINITY
        }
    }

    pub fn raw_dec(self, rhs: Self) -> Self {
        if self < LS_INFINITY {
            self - rhs
        } else {
            self
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

/// Returns true if no intersection for sure with weak constraints
// Based on the UDBM implementation
pub fn check_weak_add(cij: RawInequality, cji: RawInequality) -> bool {
    cij != LS_INFINITY && cji != LS_INFINITY && (cij + cji - (cij & cji & 1.into())) < LE_ZERO
}

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

impl From<RawInequality> for Inequality {
    fn from(raw: RawInequality) -> Self {
        let bound = raw.bound();
        if raw.is_strict() {
            Self::LS(bound)
        } else {
            Self::LE(bound)
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

impl From<RawInequality> for InnerRawInequality {
    fn from(inner: RawInequality) -> Self {
        inner.inner
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

    pub fn is_strict(&self) -> bool {
        match self {
            Inequality::LS(_) => true,
            Inequality::LE(_) => false,
        }
    }

    pub fn negated_bound(self) -> Self {
        match self {
            Inequality::LS(bound) => Inequality::LE(-bound),
            Inequality::LE(bound) => Inequality::LS(-bound),
        }
    }

    pub fn strictness_str(&self) -> &'static str {
        match self {
            Inequality::LS(_) => "<",
            Inequality::LE(_) => "<=",
        }
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

pub struct Conjunction {
    pub constraints: Vec<Constraint>,
}

impl Conjunction {
    pub fn unconstrained() -> Self {
        Self::new(vec![])
    }

    pub fn new(constraints: Vec<Constraint>) -> Self {
        Self { constraints }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Constraint> {
        self.constraints.iter()
    }

    pub fn to_string_with_naming(&self, naming: Option<&HashMap<ClockIndex, String>>) -> String {
        if self.constraints.is_empty() {
            "true".to_string()
        } else {
            let mut first = true;
            let mut result = String::new();
            for constraint in &self.constraints {
                if first {
                    first = false;
                } else {
                    result.push_str(" && ");
                }
                result.push_str(&constraint.to_string_with_naming(naming));
            }
            result
        }
    }
}

impl Display for Conjunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_string_with_naming(None))
    }
}

pub struct Disjunction {
    pub conjunctions: Vec<Conjunction>,
}

impl Disjunction {
    pub fn unconstrained() -> Self {
        Self::new(vec![Conjunction::unconstrained()])
    }

    pub fn new(conjunctions: Vec<Conjunction>) -> Self {
        Self { conjunctions }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Conjunction> {
        self.conjunctions.iter()
    }

    pub fn to_string_with_naming(&self, naming: Option<&HashMap<ClockIndex, String>>) -> String {
        if self.conjunctions.is_empty() {
            "false".to_string()
        } else if self.conjunctions.len() == 1 {
            self.conjunctions[0].to_string_with_naming(naming)
        } else {
            let mut first = true;
            let mut result = String::new();
            for conjunction in &self.conjunctions {
                if first {
                    first = false;
                } else {
                    result.push_str(" || ");
                }
                result.push_str(&format!("({})", conjunction.to_string_with_naming(naming)));
            }
            result
        }
    }
}

impl Display for Disjunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_string_with_naming(None))
    }
}

/// Represents a constraint of the form `i-j ≤/< c`. Where `raw_ineq` represents c and the strictness
pub struct Constraint {
    pub i: ClockIndex,
    pub j: ClockIndex,
    pub(crate) raw_ineq: RawInequality,
}

impl Constraint {
    pub fn new(i: ClockIndex, j: ClockIndex, ineq: RawInequality) -> Self {
        Self {
            i,
            j,
            raw_ineq: ineq,
        }
    }

    pub fn ineq(&self) -> Inequality {
        self.raw_ineq.into()
    }

    pub fn to_string_with_naming(&self, naming: Option<&HashMap<ClockIndex, String>>) -> String {
        assert!(!self.raw_ineq.is_inf());
        let ineq = self.ineq();
        if self.j == 0 {
            assert_ne!(self.i, 0);
            let i_name = naming
                .and_then(|naming| naming.get(&self.i).cloned())
                .unwrap_or(format!("c:{}", self.i));
            format!("{}{}", i_name, ineq)
        } else if self.i == 0 {
            let j_name = naming
                .and_then(|naming| naming.get(&self.j).cloned())
                .unwrap_or(format!("c:{}", self.j));
            let bound = -ineq.bound();
            let op = ineq.strictness_str();

            // 0-j <= c -> -j <= c -> -j-c <= 0 -> -c <= j

            format!("{bound}{op}{j_name}")
        } else {
            let i_name = naming
                .and_then(|naming| naming.get(&self.i).cloned())
                .unwrap_or(format!("c:{}", self.i));
            let j_name = naming
                .and_then(|naming| naming.get(&self.j).cloned())
                .unwrap_or(format!("c:{}", self.j));

            if ineq.bound() == 0 {
                format!("{}{}{}", i_name, ineq.strictness_str(), j_name)
            } else {
                format!("{}-{}{}", i_name, j_name, ineq)
            }
        }
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_string_with_naming(None))
    }
}
