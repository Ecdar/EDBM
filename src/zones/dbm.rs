use std::{
    collections::hash_map::DefaultHasher,
    fmt::{Debug, Display},
    ops::{Index, IndexMut},
};

use crate::{
    expensive_assert,
    util::{
        bit_conversion::BitField,
        bounds::Bounds,
        constraints::{
            bound_constants::INFINITY,
            raw_constants::{LE_ZERO, LS_INFINITY},
            Bound, ClockIndex, Conjunction, Constraint, Inequality, RawInequality,
        },
    },
    zones::util::worst_value,
};
use std::hash::{Hash, Hasher};

use super::{
    minimal_graph::{get_dbm_bit_matrix, BitMatrix},
    Federation, OwnedFederation,
};

pub trait ImmutableDBM: Sized {
    fn as_valid_ref(&self) -> &DBM<Valid>;
    fn owned_fed_clone(fed: &Federation<Self>) -> OwnedFederation;
}

impl ImmutableDBM for DBM<Valid> {
    #[inline(always)]
    fn as_valid_ref(&self) -> &DBM<Valid> {
        self
    }

    #[inline(always)]
    fn owned_fed_clone(fed: &Federation<Self>) -> OwnedFederation {
        fed.clone()
    }
}

pub trait DBMState: Sized {}

#[derive(Clone)]
pub struct DBM<State: DBMState> {
    pub dim: ClockIndex,
    data: Vec<RawInequality>,
    state: State,
}

#[derive(PartialEq, Eq)]
pub enum DBMRelation {
    Different,
    Superset,
    Subset,
    Equal,
}

impl Debug for DBMRelation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Different => write!(f, "Different"),
            Self::Superset => write!(f, "Superset"),
            Self::Subset => write!(f, "Subset"),
            Self::Equal => write!(f, "Equal"),
        }
    }
}

// Based on the UDBM implementation
fn try_subset(dbm1: &[RawInequality], dbm2: &[RawInequality], i: usize, n: usize) -> DBMRelation {
    for k in i..n {
        if dbm1[k] > dbm2[k] {
            return DBMRelation::Different;
        }
    }

    DBMRelation::Subset
}

// Based on the UDBM implementation
fn try_superset(dbm1: &[RawInequality], dbm2: &[RawInequality], i: usize, n: usize) -> DBMRelation {
    for k in i..n {
        if dbm1[k] < dbm2[k] {
            return DBMRelation::Different;
        }
    }

    DBMRelation::Superset
}

/// A Dirty DBM is not necessarily closed nor non-empty.
///
/// It automatically maintains a list of mutated clocks which is used to to efficiently `close` the DBM into a Valid DBM
#[derive(Clone)]
pub struct Dirty {
    ci: Option<ClockIndex>,
    cj: Option<ClockIndex>,
    touched: BitField,
}

impl Dirty {
    #[must_use]
    pub fn new_clean(dim: usize) -> Self {
        Dirty {
            ci: None,
            cj: None,
            touched: BitField::zeros(dim),
        }
    }

    #[must_use]
    pub fn new_dirty(dim: usize) -> Self {
        Dirty {
            ci: None,
            cj: None,
            touched: BitField::ones(dim),
        }
    }

    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.touched.is_empty()
    }

    #[must_use]
    pub fn is_dirty(&self) -> bool {
        !self.is_clean()
    }
}

// Need to store the dirty indices eventually

/// A Valid DBM is always closed and never empty
#[derive(Clone)]
pub struct Valid {
    hash: Option<u64>,
}

/// An Unsafe DBM is not necessarily closed nor non-empty.
///
/// Once unsafe operations are done the DBM can be asserted valid (Closed, non-empty, ok diagonal etc.) using the unsafe fn `assert_valid`
pub(super) struct Unsafe {
    changed: bool,
    hash: Option<u64>,
}

impl DBMState for Valid {}
impl DBMState for Dirty {}
impl DBMState for Unsafe {}

macro_rules! check_indices {
    ($self:expr, $e:expr) => {
            assert!($e < $self.dim);
    };

    ($self:expr, $e:expr, $($es:expr),+) => {{
        check_indices! { $self, $e }
        check_indices! { $self, $($es),+ }
    }};
}

impl DBM<Valid> {
    #[must_use]
    pub fn hash(&mut self) -> u64 {
        self.state.hash.unwrap_or_else(|| self.calculate_hash())
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn can_delay_indefinitely(&self) -> bool {
        for i in 1..self.dim {
            if self[(i, 0)] < LS_INFINITY {
                return false;
            }
        }

        true
    }

    /// Update the given `bounds` with the clock bounds of this DBM
    pub fn update_bounds(&self, bounds: &mut Bounds) {
        assert_eq!(self.dim, bounds.dim());
        for i in 0..self.dim {
            for j in 0..self.dim {
                // i-j <?= bound
                if i == j {
                    continue;
                }

                let bound = self[(i, j)];

                // If the upper bound is positive and finite we add it to the bounds
                if i != 0 && !bound.is_inf() && bound.bound() >= 0 {
                    bounds.add_upper(i, bound.bound())
                }

                // If the lower bound is non-negative (after negating) we add it to the bounds
                // Recall we go from `i-j <?= bound` to `i-bound <?= j`
                if j != 0 && bound.bound() <= 0 {
                    bounds.add_lower(j, -bound.bound())
                }
            }
        }
    }

    /// Returns the clock bounds of this DBM
    pub fn get_bounds(&self) -> Bounds {
        let mut bounds = Bounds::new(self.dim);
        self.update_bounds(&mut bounds);
        bounds
    }

    fn calculate_hash(&mut self) -> u64 {
        let mut s = DefaultHasher::new();

        self.dim.hash(&mut s);
        self.data.hash(&mut s);

        let hash = s.finish();
        self.state.hash = Some(hash);
        hash
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn relation_to(&self, other: &Self) -> DBMRelation {
        use DBMRelation::*;
        assert_eq!(self.dim, other.dim);
        let dim = self.dim;

        let dbm1 = &self.data;
        let dbm2 = &other.data;

        let n = dim * dim - 1;

        for i in 1..n {
            if dbm1[i] != dbm2[i] {
                if dbm1[i] > dbm2[i] {
                    return try_superset(dbm1, dbm2, i, n);
                } else {
                    return try_subset(dbm1, dbm2, i, n);
                }
            }
        }

        Equal
    }

    #[must_use]
    pub fn subset_eq(&self, other: &Self) -> bool {
        assert_eq!(self.dim, other.dim);
        let dim = self.dim;
        let n = dim * dim - 1;

        try_subset(&self.data, &other.data, 1, n) == DBMRelation::Subset
    }

    #[must_use]
    pub fn superset_eq(&self, other: &Self) -> bool {
        assert_eq!(self.dim, other.dim);
        let dim = self.dim;
        let n = dim * dim - 1;

        try_superset(&self.data, &other.data, 1, n) == DBMRelation::Superset
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn equals(&self, other: &Self) -> bool {
        assert_eq!(self.dim, other.dim);
        let dim = self.dim;

        let dbm1 = &self.data;
        let dbm2 = &other.data;

        let n = dim * dim - 1;

        for i in 1..n {
            if dbm1[i] != dbm2[i] {
                return false;
            }
        }

        true
    }

    /// Constrains the Valid DBM with `dbm[i,j]=constraint` and closes it immediately so it remains Valid.
    // Based on the UDBM implementation
    #[must_use]
    pub fn constrain_and_close_raw(
        self,
        i: ClockIndex,
        j: ClockIndex,
        constraint: RawInequality,
    ) -> Option<Self> {
        if self[(i, j)] > constraint {
            let mut dbm = self.make_unsafe();
            dbm[(i, j)] = constraint;
            if constraint.as_negated() >= dbm[(j, i)] {
                // the new DBM is empty
                return None;
            }

            let res = dbm.close_ij(i, j);

            return res;
        }

        Some(self)
    }

    /// Constrains the Valid DBM with `dbm[i,j]=constraint` and closes it immediately so it remains Valid.
    #[must_use]
    pub fn constrain_and_close(
        self,
        i: ClockIndex,
        j: ClockIndex,
        constraint: Inequality,
    ) -> Option<Self> {
        check_indices!(self, i, j);

        self.constrain_and_close_raw(i, j, constraint.into())
    }

    /// Constrains the DBM with `dbm[i,j]=constraint` without closing it afterwards
    #[must_use]
    pub fn constrain(
        self,
        i: ClockIndex,
        j: ClockIndex,
        constraint: Inequality,
    ) -> Option<DBM<Dirty>> {
        self.make_dirty().constrain(i, j, constraint)
    }

    /// Constrains the DBM with `dbm[i,j]=constraint` without closing it afterwards
    #[must_use]
    pub fn constrain_raw(
        self,
        i: ClockIndex,
        j: ClockIndex,
        constraint: RawInequality,
    ) -> Option<DBM<Dirty>> {
        self.make_dirty().constrain_raw(i, j, constraint)
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn tighten(self, i: ClockIndex, j: ClockIndex, constraint: RawInequality) -> Self {
        debug_assert!(self[(i, j)] > constraint && constraint.as_negated() < self[(j, i)]);

        let mut dbm = self.make_unsafe();
        dbm[(i, j)] = constraint;
        dbm.close_ij(i, j).expect("Tightening must never be empty")
    }

    #[must_use]
    pub fn from_conjunction(conjunction: &Conjunction, dim: ClockIndex) -> DBM<Valid> {
        let mut dbm = DBM::universe(dim);
        for cons in conjunction.iter() {
            dbm = dbm.tighten(cons.i, cons.j, cons.raw_ineq);
        }

        dbm
    }

    #[must_use]
    pub fn new(dim: ClockIndex, value: Inequality) -> DBM<Dirty> {
        assert!(dim > 0);
        DBM {
            dim,
            data: vec![value.into(); dim * dim],
            state: Dirty::new_dirty(dim),
        }
    }

    #[must_use]
    pub fn new_raw(dim: ClockIndex, value: RawInequality) -> DBM<Dirty> {
        assert!(dim > 0);
        DBM {
            dim,
            data: vec![value; dim * dim],
            state: Dirty::new_dirty(dim),
        }
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn zero(dim: ClockIndex) -> DBM<Valid> {
        assert!(dim > 0);
        DBM {
            dim,
            data: vec![LE_ZERO; dim * dim],
            state: Valid { hash: None },
        }
    }

    // Based on the UDBM implementation of `init`
    #[must_use]
    pub fn universe(dim: ClockIndex) -> Self {
        assert!(dim > 0);
        let mut inf = DBM {
            dim,
            data: vec![LS_INFINITY; dim * dim],
            state: Unsafe {
                changed: false,
                hash: None,
            },
        };

        for i in 0..dim {
            inf[(0, i)] = LE_ZERO;
            inf[(i, i)] = LE_ZERO;
        }

        unsafe { inf.assert_valid() }
    }

    #[must_use]
    pub fn init(dim: ClockIndex) -> DBM<Valid> {
        let res = DBM::zero(dim);
        res.up()
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn up(self) -> Self {
        let mut dbm = self.make_unsafe();

        for i in 1..dbm.dim {
            dbm[(i, 0)] = LS_INFINITY;
        }

        unsafe { dbm.assert_valid() }
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn down(self) -> Self {
        let mut dbm = self.make_unsafe();

        for j in 1..dbm.dim {
            if dbm[(j, 0)] < LE_ZERO {
                dbm[(j, 0)] = LE_ZERO;

                for i in 1..dbm.dim {
                    if dbm[(0, j)] > dbm[(i, j)] && !dbm[(0, i)].is_inf() {
                        dbm[(0, j)] = dbm[(i, j)];
                    }
                }
            }
        }

        unsafe { dbm.assert_valid() }
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn intersection(self, src: &Self) -> Option<Self> {
        assert_eq!(self.dim, src.dim);
        let dim = self.dim;

        let mut dst = self.make_dirty();

        for i in 0..dim {
            for j in 0..dim {
                if dst[(i, j)] > src[(i, j)] {
                    dst[(i, j)] = src[(i, j)];
                    if src[(i, j)].as_negated() >= dst[(j, i)] {
                        return None;
                    }
                }
            }
        }
        dst.close()
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn convex_union(self, other: &Self) -> Self {
        assert_eq!(self.dim, other.dim);
        let dim = self.dim;

        let mut dbm = self.make_unsafe();

        for i in 0..dim {
            for j in 0..dim {
                if dbm[(i, j)] < other[(i, j)] {
                    dbm[(i, j)] = other[(i, j)];
                }
            }
        }
        unsafe { dbm.assert_valid() }
    }

    #[must_use]
    pub fn has_intersection(&self, dbm2: &Self) -> bool {
        self.maybe_intersects(dbm2) && self.clone().intersection(dbm2).is_some()
    }

    // Based on the UDBM implementation of `intersects``
    pub(super) fn maybe_intersects(&self, dbm2: &Self) -> bool {
        assert_eq!(self.dim, dbm2.dim);
        let dbm1 = self;

        for i in 1..self.dim {
            for j in 0..i {
                let dbm1_ij = dbm1[(i, j)];
                if dbm1_ij != LS_INFINITY && dbm1_ij.as_negated() >= dbm2[(j, i)] {
                    return false;
                }
                let dbm2_ij = dbm2[(i, j)];
                if dbm2_ij != LS_INFINITY && dbm2_ij.as_negated() >= dbm1[(j, i)] {
                    return false;
                }
            }
        }

        true
    }

    #[must_use]
    pub fn satisfies(&self, i: ClockIndex, j: ClockIndex, constraint: Inequality) -> bool {
        self.satisfies_raw(i, j, constraint.into())
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn satisfies_raw(&self, i: ClockIndex, j: ClockIndex, constraint: RawInequality) -> bool {
        assert!(i != j);
        !(self[(i, j)] > constraint && constraint.as_negated() >= self[(j, i)])
    }

    // Based on the UDBM implementation
    pub fn extrapolate_max_bounds(self, bounds: &Bounds) -> Self {
        let mut dbm = self.make_unsafe();
        let mut changed = false;
        use Inequality::*;

        // 1st row
        for j in 1..dbm.dim {
            if let Some(max_j) = bounds.get_max(j) {
                if dbm[(0, j)].bound() < -max_j {
                    dbm[(0, j)] = if max_j >= 0 {
                        LS(-max_j).into()
                    } else {
                        LE_ZERO
                    };
                    changed = true;
                }
            } else {
                dbm[(0, j)] = LE_ZERO;
            }
        }

        // other rows
        for i in 1..dbm.dim {
            for j in 0..dbm.dim {
                if i != j {
                    if let Some(max_j) = bounds.get_max(j) {
                        let max_i = bounds.get_max(i);
                        let bound = dbm[(i, j)].bound();
                        if (max_i.is_none() || bound > max_i.unwrap()) && bound != INFINITY {
                            dbm[(i, j)] = LS_INFINITY;
                            changed |= max_i.is_some();
                        } else if bound < -max_j {
                            dbm[(i, j)] = LS(-max_j).into();
                            changed = true;
                        }
                    } else {
                        dbm[(i, j)] = dbm[(i, 0)];
                    }
                }
            }
        }

        if changed {
            dbm.close_after_extrapolate(bounds)
        } else {
            unsafe { dbm.assert_valid() }
        }
    }

    // Based on the UDBM implementation
    /// Perform extrapolation on the dbm based on the lower and upper bounds of the clocks.
    /// # Warning
    /// Use with caution. Lower and upper bound based extrapolation is not sound for all types of reachability problems.
    #[must_use]
    pub fn extrapolate_lu_bounds(self, bounds: &Bounds) -> Self {
        let mut dbm = self.make_unsafe();
        let mut changed = false;
        use Inequality::*;

        // 1st row
        for j in 1..dbm.dim {
            if let Some(upper_j) = bounds.get_upper(j) {
                if dbm[(0, j)].bound() < -upper_j {
                    dbm[(0, j)] = if upper_j >= 0 {
                        LS(-upper_j).into()
                    } else {
                        LE_ZERO
                    };
                    changed = true;
                }
            } else {
                dbm[(0, j)] = LE_ZERO;
            }
        }

        // other rows
        for i in 1..dbm.dim {
            for j in 0..dbm.dim {
                if i != j {
                    if let Some(upper_j) = bounds.get_upper(j) {
                        let lower_i = bounds.get_lower(i);
                        let bound = dbm[(i, j)].bound();
                        if (lower_i.is_none() || bound > lower_i.unwrap()) && bound != INFINITY {
                            dbm[(i, j)] = LS_INFINITY;
                            changed |= lower_i.is_some();
                        } else if bound < -upper_j {
                            dbm[(i, j)] = LS(-upper_j).into();
                            changed = true;
                        }
                    } else {
                        dbm[(i, j)] = dbm[(i, 0)];
                    }
                }
            }
        }

        if changed {
            dbm.close_after_extrapolate(bounds)
        } else {
            unsafe { dbm.assert_valid() }
        }
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn update_clock_val(self, clock: ClockIndex, val: Bound) -> Self {
        assert!(clock > 0);

        use Inequality::*;
        let mut dbm = self.make_unsafe();

        dbm[(clock, 0)] = LE(val).into();
        dbm[(0, clock)] = LE(-val).into();
        for i in 1..dbm.dim {
            dbm[(clock, i)] = dbm[(clock, 0)].add_raw(dbm[(0, i)]);
            dbm[(i, clock)] = dbm[(i, 0)].add_raw(dbm[(0, clock)]);
        }

        unsafe { dbm.assert_valid() }
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn update_clock_clock(self, clock_i: ClockIndex, clock_j: ClockIndex) -> Self {
        assert!(clock_i > 0 && clock_j > 0);

        if clock_i == clock_j {
            return self;
        }
        let mut dbm = self.make_unsafe();

        for k in 0..dbm.dim {
            if clock_i != k {
                dbm[(clock_i, k)] = dbm[(clock_j, k)];
                dbm[(k, clock_i)] = dbm[(k, clock_j)];
            }
        }

        unsafe { dbm.assert_valid() }
    }

    // Based on the UDBM implementation
    fn compute_tables(&self, src_clocks: &Vec<bool>, dst_clocks: &Vec<bool>) -> (Vec<ClockIndex>, Vec<ClockIndex>) {
        let mut dst_to_src = Vec::<ClockIndex>::default();
        let mut src_to_dst = Vec::<ClockIndex>::default();
        let mut src_ind = 0;
        assert_eq!(src_clocks.len(), dst_clocks.len());

        for (src, dst) in src_clocks.iter().zip(dst_clocks.iter()){
            if *dst {
                src_to_dst.push(dst_to_src.len());
                if *src {
                    dst_to_src.push(src_ind);
                }
                else {
                    dst_to_src.push(0);
                }
            }
            else {
                src_to_dst.push(0);
            }

            src_ind += 1;
        };

        return (src_to_dst, dst_to_src);
    }

    // Based on the UDBM implementation
    fn update_dbm(&mut self, src: &DBM<Valid>, dst_to_src: &Vec<ClockIndex>) {
        self.data[0] = LE_ZERO;

        // Clocks [0,j]
        for j in 1..self.dim {
            if dst_to_src[j] == 0
            {
                self.data[j] = LE_ZERO;
            }
            else
            {
                self.data[j] = src.data[dst_to_src[j]];
            }
        }

        for i in 1..self.dim {
            if dst_to_src[i] != 0 { // If copy from src.
                let constraint0 = src.data[src.dim * dst_to_src[i]];
                // Clock [i, 0]
                self.data[i * self.dim] = constraint0;

                for j in 1..self.dim {
                    if dst_to_src[j] == 0
                    {
                        self.data[j + i * self.dim] = constraint0;
                    }
                    else {
                        self.data[j + i * self.dim] = src.data[dst_to_src[j] + src.dim * dst_to_src[i]];
                    }
                }
            }
            else { // Insert new row.
                for j in 0..self.dim {
                    self.data[j + i * self.dim] = LS_INFINITY;
                }
            }
            self.data[i + i * self.dim] = LE_ZERO;
        }
    }

    // Based on the UDBM implementation
    /// 0,      1,      2,      3,      4
    /// 5,      6,      7,      8,      9
    /// 10,     11,     12,     13,     14
    /// 15,     16,     17,     18,     19
    /// 20,     21,     22,     23,     24
    /// is redrawn into
    /// 0,      1,      4,       0,      0
    /// 5,      0,      9,       5,      5
    /// 10,     11,     0,       10,     10
    /// inf,    inf,    inf,     0,      inf
    /// inf,    inf,    inf,     inf,    0
    /// With clock inputs
    /// src_clocks: [true, true, true, false, false, false, false]
    /// dst_clocks: [true, true, true, false, false, true, true]
    /// It will also return a mapping of the src clocks to the dst clocks.
    /// src_to_dst: [0, 1, 2, 0, 0, 3, 4]
    pub fn shrink_expand(&self, src_clocks: &Vec<bool>, dst_clocks: &Vec<bool>) -> (DBM<Valid>, Vec<ClockIndex>) {
        assert_eq!(src_clocks.len(), dst_clocks.len());
        let (src_to_dst, dst_to_src) = self.compute_tables(src_clocks, dst_clocks);
        let mut dst = DBM::init(dst_to_src.len());
        dst.update_dbm(self, &dst_to_src);
        return (dst, src_to_dst);
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn update_increment(self, clock: ClockIndex, inc: Bound) -> Self {
        assert!(clock > 0);
        if inc == 0 {
            return self;
        }
        use Inequality::*;
        let inc = LS(inc).into();

        let mut dbm = self.make_unsafe();

        for i in 0..dbm.dim {
            if dbm[(clock, i)] < LS_INFINITY {
                dbm[(clock, i)] += inc;
            }

            if dbm[(i, clock)] < LS_INFINITY {
                dbm[(i, clock)] -= inc;
            }
        }

        unsafe { dbm.assert_valid() }
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn update(self, i: ClockIndex, j: ClockIndex, val: Bound) -> Self {
        assert!(i > 0 && j > 0);
        if i == j {
            return self.update_increment(i, val);
        }

        if val == 0 {
            return self.update_clock_clock(i, j);
        }

        use Inequality::*;
        let val: RawInequality = LS(val).into();

        let mut dbm = self.make_unsafe();

        for k in 0..dbm.dim {
            dbm[(i, k)] = dbm[(j, k)].raw_inc(val);
            dbm[(k, i)] = dbm[(k, j)].raw_dec(val);
        }
        // Restore diagonal
        dbm[(i, i)] = LE_ZERO;

        unsafe { dbm.assert_valid() }
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn free_clock(self, clock: ClockIndex) -> Self {
        check_indices!(self, clock);
        assert!(clock > 0);

        let mut dbm = self.make_unsafe();
        for i in 0..dbm.dim {
            if i != clock {
                dbm[(clock, i)] = LS_INFINITY;
                dbm[(i, clock)] = dbm[(i, 0)];
            }
        }

        unsafe { dbm.assert_valid() }
    }

    pub(super) fn make_dirty(self) -> DBM<Dirty> {
        DBM {
            dim: self.dim,
            data: self.data,
            state: Dirty::new_clean(self.dim),
        }
    }

    /// Tighten the dbm with the negated constraints of rhs dbm, potentially splitting the dbm in two.
    // Based on the UDBM implementation
    #[must_use]
    pub fn subtract_dbm(self, rhs: &DBM<Valid>) -> Vec<DBM<Valid>> {
        if self.maybe_intersects(rhs) {
            let matrix = get_dbm_bit_matrix(rhs);
            if matrix.n_cons == 0 {
                // dbm2 is unconstrained => result = empty
                return vec![];
            }
            self.internal_subtract_dbm(rhs, &matrix)
        } else {
            vec![self]
        }
    }

    // Based on the UDBM implementation
    pub(super) fn internal_subtract_dbm(
        self,
        dbm2: &DBM<Valid>,
        matrix: &BitMatrix,
    ) -> Vec<DBM<Valid>> {
        let dim = self.dim;
        let mut dbm1 = self;
        let n_cons = matrix.n_cons;
        let mut indices: Vec<_> = matrix
            .bits
            .get_ijs(dim, n_cons as usize)
            .into_iter()
            .filter(|&index| {
                let (i, j) = index;

                dbm2[(i, j)] < dbm1[(i, j)]
            })
            .collect();

        let mut n_cons = indices.len();

        let mut result = vec![];

        let mut i = 0;
        let mut j = 0;
        let mut c = None;

        while n_cons > 0 {
            // Find constraint i,j to subtract
            let mut bestv: RawInequality = RawInequality::MAX;
            let mut k = 0;

            while k < n_cons {
                let (ci, cj) = indices[k];

                // If dbm2 outside dbm1 then no more subtraction.
                debug_assert!(dbm2[(ci, cj)] != LS_INFINITY);
                if dbm2[(ci, cj)].as_negated() >= dbm1[(cj, ci)] {
                    result.push(dbm1);
                    return result;
                }

                if dbm2[(ci, cj)] >= dbm1[(ci, cj)] {
                    n_cons -= 1;
                    if n_cons == 0 {
                        return result;
                    }
                    // Playing with the order is sometimes better, sometimes worse.
                    indices[k] = indices[n_cons];
                    continue;
                }

                // need to recompute every time because dbm1 changes
                if bestv > -LS_INFINITY {
                    if dbm1[(ci, cj)] == LS_INFINITY {
                        bestv = -LS_INFINITY;
                        i = ci;
                        j = cj;
                        c = Some(k);
                        // Don't break the loop since the 1st test may
                        // cancel the split.
                    } else {
                        let cv = worst_value(&dbm1, dbm2, ci, cj);

                        if bestv > cv {
                            bestv = cv;
                            i = ci;
                            j = cj;
                            c = Some(k);
                        }
                    }
                }
                k += 1;
            }

            let c = c.unwrap(); // Found one index
            assert!(c < n_cons);
            n_cons -= 1;
            indices[c] = indices[n_cons]; // Swap the last

            debug_assert!(i != j);
            debug_assert!(dbm2[(i, j)] != LS_INFINITY);
            // Subtraction for dbm2[i,j]
            if dbm2[(i, j)] < dbm1[(i, j)] {
                let neg_cons = dbm2[(i, j)].as_negated();

                debug_assert!(neg_cons < dbm1[(j, i)]);
                if n_cons == 0 {
                    // is last constraint?
                    result.push(dbm1.tighten(j, i, neg_cons));
                    return result;
                }
                result.push(dbm1.clone().tighten(j, i, neg_cons));
                dbm1 = dbm1.tighten(i, j, dbm2[(i, j)]) // continue with remainders
            }
        }

        result
    }

    fn make_unsafe(self) -> DBM<Unsafe> {
        let dbm = DBM {
            dim: self.dim,
            data: self.data,
            state: Unsafe {
                changed: false,
                hash: self.state.hash,
            },
        };

        expensive_assert!(dbm.is_diagonal_ok_and_clocks_positive());

        dbm
    }
}

impl TryInto<DBM<Valid>> for DBM<Dirty> {
    type Error = ();

    fn try_into(self) -> Result<DBM<Valid>, Self::Error> {
        self.close().ok_or(())
    }
}

impl DBM<Dirty> {
    /// Constrains the DBM with `dbm[i,j]=constraint` without closing it afterwards
    // Based on the UDBM implementation
    #[must_use]
    pub fn constrain_raw(
        mut self,
        i: ClockIndex,
        j: ClockIndex,
        constraint: RawInequality,
    ) -> Option<Self> {
        if self[(i, j)] > constraint {
            self[(i, j)] = constraint;
            if constraint.as_negated() >= self[(j, i)] {
                // the new DBM is empty
                return None;
            }
            return Some(self);
        }

        Some(self)
    }

    /// Constrains the DBM with `dbm[i,j]=constraint` without closing it afterwards
    #[must_use]
    pub fn constrain(self, i: ClockIndex, j: ClockIndex, constraint: Inequality) -> Option<Self> {
        check_indices!(self, i, j);

        self.constrain_raw(i, j, constraint.into())
    }

    // Based on the UDBM implementation
    fn close_touched(self) -> Option<DBM<Valid>> {
        if self.state.is_clean() || self.dim < 1 {
            return Some(unsafe { self.make_unsafe().assert_valid() });
        }
        let dirty_clocks = self.state.touched.indices();
        if let (Some(i), Some(j)) = (self.state.ci, self.state.cj) {
            // TODO: maybe this is safe?
            debug_assert_eq!(dirty_clocks.len(), 2);
            return self.make_unsafe().close_ij(i, j);
        }

        let mut dbm = self.make_unsafe();

        for k in dirty_clocks {
            for i in 0..dbm.dim {
                // Skip diagonal
                if i != k {
                    let dbm_ik = dbm[(i, k)];

                    if dbm_ik != LS_INFINITY {
                        for j in 0..dbm.dim {
                            let dbm_kj = dbm[(k, j)];

                            if dbm_kj != LS_INFINITY {
                                let dbm_ikkj = dbm_ik.add_raw(dbm_kj);
                                if dbm[(i, j)] > dbm_ikkj {
                                    dbm[(i, j)] = dbm_ikkj;
                                }
                            }
                        }
                    }

                    if dbm[(i, i)] < LE_ZERO {
                        // the new DBM is empty
                        return None;
                    }
                }
            }
        }

        Some(unsafe { dbm.assert_valid() })
    }

    #[must_use]
    pub fn close(self) -> Option<DBM<Valid>> {
        self.close_touched()
    }

    #[allow(unused)]
    // Based on the UDBM implementation
    fn close_all(mut self) -> Option<DBM<Valid>> {
        let mut dbm = self.make_unsafe();

        for k in 0..dbm.dim {
            for i in 0..dbm.dim {
                if i != k {
                    let dbm_ik = dbm[(i, k)];
                    if dbm_ik != LS_INFINITY {
                        for j in 0..dbm.dim {
                            let dbm_kj = dbm[(k, j)];

                            if dbm_kj != LS_INFINITY {
                                let dbm_ikkj = dbm_ik.add_raw(dbm_kj);
                                if dbm[(i, j)] > dbm_ikkj {
                                    dbm[(i, j)] = dbm_ikkj;
                                }
                            }
                        }
                    }

                    if dbm[(i, i)] < LE_ZERO {
                        // the new DBM is empty
                        return None;
                    }
                }

                assert!(dbm[(i, i)] == LE_ZERO);
            }
        }
        // By definition the method closes the DBM
        Some(unsafe { dbm.assert_valid() })
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn up(mut self) -> Self {
        for i in 1..self.dim {
            self[(i, 0)] = LS_INFINITY;
        }

        self
    }

    fn make_unsafe(self) -> DBM<Unsafe> {
        let dbm = DBM {
            dim: self.dim,
            data: self.data,
            state: Unsafe {
                changed: self.state.is_dirty(),
                hash: None,
            },
        };

        expensive_assert!(dbm.is_diagonal_ok_and_clocks_positive());

        dbm
    }
}

impl DBM<Unsafe> {
    // Based on the UDBM implementation
    #[must_use]
    pub fn is_empty(&self) -> bool {
        for i in 0..self.dim {
            if self[(i, i)] < LE_ZERO {
                return true;
            }
        }
        false
    }

    // Based on the UDBM implementation
    #[cfg(feature = "expensive_asserts")]
    fn is_diagonal_ok_and_clocks_positive(&self) -> bool {
        for i in 0..self.dim {
            if self[(i, i)] > LE_ZERO {
                println!("Non-zero diagonal");
                return false;
            }
        }

        for j in 0..self.dim {
            if self[(0, j)] > LE_ZERO {
                println!("Negative valued clock");
                return false;
            }
        }

        true
    }

    // Based on the UDBM implementation
    #[must_use]
    pub fn is_valid(&self) -> bool {
        if !self.is_closed() {
            println!("Not closed");
            return false;
        }

        if self.is_empty() {
            println!("Empty");
            return false;
        }

        for j in 0..self.dim {
            if self[(0, j)] > LE_ZERO {
                println!("Negative valued clock");
                return false;
            }
        }

        true
    }

    // Based on the UDBM implementation
    fn is_closed(&self) -> bool {
        for k in 0..self.dim {
            for i in 0..self.dim {
                if self[(i, k)] < LS_INFINITY {
                    for j in 0..self.dim {
                        if self[(k, j)] < LS_INFINITY
                            && self[(i, j)] > self[(i, k)].add_raw(self[(k, j)])
                        {
                            return false;
                        }
                    }
                }
            }
        }

        true
    }

    /// Efficient close after adding single constraint
    ///
    /// Warning: Order of `b` and `a` matters! When `DBM(i,j) = c` call `self.close_ij(b=i,a=j)`
    // Based on the UDBM implementation
    fn close_ij(self, b: ClockIndex, a: ClockIndex) -> Option<DBM<Valid>> {
        check_indices!(self, b, a);
        assert!(a != b);

        if !self.state.changed {
            return Some(unsafe { self.assert_valid() });
        }

        let mut dbm = self;

        if dbm.dim <= 2 {
            // If only one clock do nothing
            return Some(unsafe { dbm.assert_valid() });
        }

        let dbm_ba = dbm[(b, a)];

        for j in 0..dbm.dim {
            let dbm_aj = dbm[(a, j)];
            if dbm_aj != LS_INFINITY {
                let bj = dbm_ba.add_raw(dbm_aj);
                if dbm[(b, j)] > bj {
                    dbm[(b, j)] = bj;
                }
            }
        }

        for i in 0..dbm.dim {
            let dbm_ib = dbm[(i, b)];
            if dbm_ib != LS_INFINITY {
                let ia = dbm_ib.add_raw(dbm_ba);
                if dbm[(i, a)] > ia {
                    dbm[(i, a)] = ia;
                    for j in 0..dbm.dim {
                        let dbm_aj = dbm[(a, j)];
                        if dbm_aj != LS_INFINITY {
                            let ij = ia.add_raw(dbm_aj);
                            if dbm[(i, j)] > ij {
                                dbm[(i, j)] = ij;
                            }
                        }
                    }
                }
            }
        }

        if dbm.is_empty() {
            None
        } else {
            Some(unsafe { dbm.assert_valid() })
        }
    }

    // Based on the UDBM implementation
    fn close_after_extrapolate(self, bounds: &Bounds) -> DBM<Valid> {
        let dim = self.dim;
        let mut dbm = self;
        for k in 0..dim {
            if bounds.get_max(k).is_some() {
                for i in 0..dim {
                    if i != k {
                        let dbm_ik = dbm[(i, k)];
                        if !dbm_ik.is_inf() {
                            for j in 0..dim {
                                let dbm_kj = dbm[(k, j)];
                                if !dbm_kj.is_inf() {
                                    let dbm_ikkj = dbm_ik.add_raw(dbm_kj);
                                    if dbm[(i, j)] > dbm_ikkj {
                                        dbm[(i, j)] = dbm_ikkj;
                                    }
                                }
                            }
                        }
                        assert!(dbm[(i, i)] >= LE_ZERO);
                    }
                    assert!(dbm[(i, i)] == LE_ZERO);
                }
            }
        }

        unsafe { dbm.assert_valid() }
    }

    /// Assert that a DBM is closed without checking (The `expensive_asserts` feature enables a (slow) check here)
    ///
    /// This method is always memory/thread safe!
    ///
    /// It is 'only' unsafe in that it can be called on an unclosed DBM (When the `expensive_asserts` feature is disabled)
    /// which breaks the preconditions on every method which requires closed DBMs (all of impl DBM<Valid>)
    unsafe fn assert_valid(self) -> DBM<Valid> {
        expensive_assert!(self.is_valid());

        let hash = if !self.state.changed {
            self.state.hash
        } else {
            None
        };

        DBM {
            dim: self.dim,
            data: self.data,
            state: Valid { hash },
        }
    }
}

impl<T: DBMState> DBM<T> {
    #[must_use]
    pub fn conjunction_of_minimal_constraints(&self) -> Conjunction {
        let (bf, n_cons) = get_dbm_bit_matrix(self).split();
        let n_cons = n_cons as usize;
        let ijs = bf.get_ijs(self.dim, n_cons);
        let mut constraints = Vec::with_capacity(n_cons);
        for (i, j) in ijs.into_iter() {
            constraints.push(Constraint::new(i, j, self[(i, j)]));
        }

        Conjunction::new(constraints)
    }
}

impl<T: DBMState> Index<(ClockIndex, ClockIndex)> for DBM<T> {
    type Output = RawInequality;

    fn index(&self, index: (ClockIndex, ClockIndex)) -> &Self::Output {
        let (x, y) = index;
        &self.data[x * self.dim + y]
    }
}

impl IndexMut<(ClockIndex, ClockIndex)> for DBM<Dirty> {
    fn index_mut(&mut self, index: (ClockIndex, ClockIndex)) -> &mut Self::Output {
        let (i, j) = index;

        if self.state.touched.is_empty() {
            self.state.ci = Some(i);
            self.state.cj = Some(j);
        } else {
            self.state.ci = None;
            self.state.cj = None;
        }

        self.state.touched.set(i);
        self.state.touched.set(j);

        &mut self.data[i * self.dim + j]
    }
}

impl IndexMut<(ClockIndex, ClockIndex)> for DBM<Unsafe> {
    fn index_mut(&mut self, index: (ClockIndex, ClockIndex)) -> &mut Self::Output {
        self.state.changed = true;
        let (x, y) = index;
        &mut self.data[x * self.dim + y]
    }
}

impl<T: DBMState> Display for DBM<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut lines = vec![];

        for i in 0..self.dim {
            let mut line = vec![];

            for j in 0..self.dim {
                line.push(format!("{}", self[(i, j)]));
            }
            lines.push(line);
        }

        let max_len = lines.iter().flatten().map(|s| s.len()).max().unwrap();
        for line in lines {
            write!(f, "[ ")?;
            for s in line {
                write!(f, "{:<max_len$}", s)?;
            }
            writeln!(f, "]")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::util::constraints::Inequality::LE;
    use crate::util::constraints::{Bound};
    use crate::util::constraints::raw_constants::{LE_ZERO, LS_INFINITY};
    use super::DBM;
    use crate::zones::rand_gen::random_dbm;
    use crate::zones::DBMRelation;

    #[test]
    fn dbm1() {
        use super::DBM;
        use crate::util::constraints::Inequality::*;

        let dbm = DBM::new(10, LE(0));
        let dbm = dbm.close().unwrap();

        assert!(dbm.has_intersection(&dbm));
    }

    #[test]
    fn dbm_up() {
        use super::DBM;
        use crate::util::constraints::Inequality::*;

        let dbm = DBM::new(3, LE(0));
        let dbm = dbm.close().unwrap();
        let old = dbm.clone();
        println!("Before: \n{}", dbm);
        let dbm = dbm.up();
        println!("After: \n{}", dbm);

        assert!(old.has_intersection(&dbm));
    }

    #[test]
    fn dbm_constrain1() {
        use super::DBM;
        use crate::util::constraints::Inequality::*;

        let dbm = DBM::init(3);
        let original = dbm.clone();
        println!("Before: \n{}", dbm);

        let dbm = dbm.constrain_and_close(1, 0, LE(2)).unwrap();

        println!("After: \n{}", dbm);

        assert!(original.has_intersection(&dbm));
    }

    #[test]
    fn dbm_constrain2() {
        use crate::util::constraints::Inequality::*;

        fn test() -> Option<()> {
            for i in 1..100 {
                let dbm1 = DBM::init(5);
                let dbm2 = dbm1.clone();
                let dbm3 = dbm1.clone();

                let dbm1 = dbm1.constrain(1, 0, LE(i))?; // Upper bound
                let dbm1 = dbm1.close()?;

                let dbm2 = dbm2.constrain_and_close(0, 1, LS(-i))?; // Lower bound
                let dbm3 = dbm3.constrain_and_close(1, 0, LE(i + 1))?; // Upper bound

                assert!(!dbm1.has_intersection(&dbm2));

                assert!(dbm1.has_intersection(&dbm3));
                assert!(dbm2.has_intersection(&dbm3));
            }

            Some(())
        }
        test().unwrap()
    }

    #[test]
    fn dbm_shrink_expand(){
        let mut src = DBM::init(5);
        for i in 1..25 {
            src.data[i] = From::from(LE(i as Bound));
        }

        let src_bit = vec![true, true, false, false, true, false, false];
        let dst_bit = vec![true, true, false, false, true, true, true];
        let (dst, src_to_dst) = src.shrink_expand(&src_bit, &dst_bit);

        assert_eq!(dst.dim, 5);
        for i in 0..5 {
            assert_eq!(dst.data[i + i * dst.dim], LE_ZERO);
        }
        assert_eq!(dst.data[0 + 4 * dst.dim], LS_INFINITY);
        assert_eq!(dst.data[1 + 4 * dst.dim], LS_INFINITY);
        assert_eq!(dst.data[2 + 4 * dst.dim], LS_INFINITY);
        assert_eq!(dst.data[3 + 4 * dst.dim], LS_INFINITY);

        assert_eq!(dst.data[0 + 1 * dst.dim], LE(5).into());
        assert_eq!(dst.data[2 + 1 * dst.dim], LE(9).into());
        assert_eq!(dst.data[3 + 1 * dst.dim], LE(5).into());
        assert_eq!(dst.data[4 + 1 * dst.dim], LE(5).into());

        assert_eq!(src_to_dst.len(), 7);
        assert_eq!(src_to_dst[0], 0);
        assert_eq!(src_to_dst[1], 1);
        assert_eq!(src_to_dst[2], 0);
        assert_eq!(src_to_dst[3], 0);
        assert_eq!(src_to_dst[4], 2);
    }

    #[test]
    fn dbm_shrink(){
        let mut src = DBM::init(5);
        for i in 1..25 {
            src.data[i] = From::from(LE(i as Bound));
        }

        let src_bit = vec![true, true, false, false, true];
        let (dst, src_to_dst) = src.shrink_expand(&src_bit, &src_bit);

        assert_eq!(dst.dim, 3);
        for i in 0..3 {
            assert_eq!(dst.data[i + i * dst.dim], LE_ZERO);
        }
        assert_eq!(dst.data[1 + 0 * dst.dim], LE(1).into());
        assert_eq!(dst.data[2 + 0 * dst.dim], LE(4).into());

        assert_eq!(dst.data[0 + 1 * dst.dim], LE(5).into());
        assert_eq!(dst.data[2 + 1 * dst.dim], LE(9).into());

        assert_eq!(dst.data[0 + 2 * dst.dim], LE(20).into());
        assert_eq!(dst.data[1 + 2 * dst.dim], LE(21).into());

        assert_eq!(src_to_dst.len(), 5);
        assert_eq!(src_to_dst[0], 0);
        assert_eq!(src_to_dst[1], 1);
        assert_eq!(src_to_dst[2], 0);
        assert_eq!(src_to_dst[3], 0);
        assert_eq!(src_to_dst[4], 2);
    }

    #[test]
    fn dbm_update() {
        let dbm = DBM::init(5);

        println!("{dbm}");
        let dbm = dbm.update_clock_val(2, 10);
        println!("{dbm}");
        let dbm = dbm.up();
        println!("{dbm}");

        //assert!(false);
    }

    #[test]
    fn dbm_subtract1() {
        use super::Inequality::*;
        let dbm1 = DBM::init(8);
        let dbm2 = dbm1
            .clone()
            .constrain_and_close(1, 0, LE(5))
            .unwrap()
            .constrain_and_close(0, 1, LE(-5))
            .unwrap();
        let res = dbm1.clone().subtract_dbm(&dbm2);

        println!("dbm1: \n{dbm1}");
        println!("dbm2: \n{dbm2}");
        println!("result:");

        for dbm in &res {
            println!("{}", dbm);
        }

        assert_eq!(res.len(), 2);
    }

    #[test]
    fn dbm_subtract2() {
        let dbm1 = DBM::init(8);
        let dbm2 = dbm1.clone();
        let res = dbm1.clone().subtract_dbm(&dbm2);

        println!("dbm1: \n{dbm1}");
        println!("dbm2: \n{dbm2}");
        println!("result:");

        for dbm in &res {
            println!("{}", dbm);
        }
        assert_eq!(res.len(), 0);
    }

    #[test]
    fn dbm_subtract3() {
        let dbm1 = DBM::init(8);
        let dbm2 = DBM::zero(8);
        let res = dbm1.clone().subtract_dbm(&dbm2);

        println!("dbm1: \n{dbm1}");
        println!("dbm2: \n{dbm2}");
        println!("result:");

        for dbm in &res {
            println!("{}", dbm);
        }

        assert_eq!(res.len(), 1);
    }

    #[test]
    fn random_dbms() {
        for _ in 0..1000 {
            let dbm = random_dbm(5);
            println!("Rand dbm: \n {dbm}");
        }
    }

    #[test]
    fn dbm_order1() {
        let zero = DBM::zero(8);
        let init = DBM::init(8);

        assert!(zero.subset_eq(&init));
        assert!(init.superset_eq(&zero));
        assert!(!zero.equals(&init));
        assert!(zero.equals(&zero));
        assert!(init.equals(&init));
        assert_eq!(zero.relation_to(&init), DBMRelation::Subset);
        assert_eq!(init.relation_to(&zero), DBMRelation::Superset);
    }

    #[test]
    fn dbm_order2() {
        use super::Inequality::*;
        let zero = DBM::zero(8);
        let init = DBM::init(8);
        let five = init
            .constrain_and_close(1, 0, LE(5))
            .unwrap()
            .constrain_and_close(0, 1, LE(-5))
            .unwrap();

        assert!(!zero.subset_eq(&five));
        assert!(!zero.superset_eq(&five));
        assert!(!zero.equals(&five));
        assert!(zero.equals(&zero));
        assert!(five.equals(&five));
        assert_eq!(zero.relation_to(&five), DBMRelation::Different);
        assert_eq!(five.relation_to(&zero), DBMRelation::Different);
    }

    const TEST_ATTEMPTS: usize = 1000;
    const DIMS: &[usize] = &[2, 5];

    #[test]
    fn rand_convex_union_test() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                let dbm1 = random_dbm(dim);
                let dbm2 = random_dbm(dim);

                let c_union = dbm1.clone().convex_union(&dbm2);

                assert!(dbm1.subset_eq(&c_union));
                assert!(dbm2.subset_eq(&c_union));
            }
        }
    }

    #[test]
    fn rand_intersection_test() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                let dbm1 = random_dbm(dim);
                let dbm2 = random_dbm(dim);

                let dbm12_opt = dbm1.clone().intersection(&dbm2);
                let dbm21_opt = dbm2.clone().intersection(&dbm1);

                assert_eq!(dbm12_opt.is_none(), dbm21_opt.is_none());

                if let Some(dbm12) = dbm12_opt {
                    let dbm21 = dbm21_opt.unwrap();
                    assert!(dbm12.equals(&dbm21));

                    assert!(dbm12.subset_eq(&dbm1));
                    assert!(dbm12.subset_eq(&dbm2));
                }
            }
        }
    }

    #[test]
    fn rand_from_constraints_test() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                let dbm1 = random_dbm(dim);
                let conj = dbm1.conjunction_of_minimal_constraints();

                let dbm2 = DBM::from_conjunction(&conj, dim);

                assert!(dbm1.equals(&dbm2));
            }
        }
    }

    /// Ensure that the bounds are correct by extrapolating with them and checking that the dbm remains unchanged.
    #[test]
    fn test_bounds() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                let dbm1 = random_dbm(dim);
                let bounds = dbm1.get_bounds();

                let dbm2 = dbm1.clone().extrapolate_max_bounds(&bounds);

                assert!(
                    dbm1.equals(&dbm2),
                    "Not equal for:\nBounds: {bounds:?}\nDBM1: {dbm1}\nDBM2: {dbm2}"
                );
            }
        }
    }
}
