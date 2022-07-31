use std::{
    collections::hash_map::DefaultHasher,
    fmt::{Debug, Display},
    ops::{Index, IndexMut},
};

use crate::{
    dbm::util::worst_value,
    util::{
        bit_conversion::BitField,
        constraints::{
            raw_constants::{LE_ZERO, LS_INFINITY},
            Bound, ClockIndex, Inequality, RawInequality,
        },
    },
};
use std::hash::{Hash, Hasher};

use super::minimal_graph::{get_dbm_bit_matrix, BitMatrix};

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

fn try_subset(
    dbm1: &Vec<RawInequality>,
    dbm2: &Vec<RawInequality>,
    i: usize,
    n: usize,
) -> DBMRelation {
    for k in i..n {
        if dbm1[k] > dbm2[k] {
            return DBMRelation::Different;
        }
    }

    DBMRelation::Subset
}

fn try_superset(
    dbm1: &Vec<RawInequality>,
    dbm2: &Vec<RawInequality>,
    i: usize,
    n: usize,
) -> DBMRelation {
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
    pub fn clean(dim: usize) -> Self {
        Dirty {
            ci: None,
            cj: None,
            touched: BitField::zeros(dim),
        }
    }

    pub fn dirty(dim: usize) -> Self {
        Dirty {
            ci: None,
            cj: None,
            touched: BitField::ones(dim),
        }
    }

    pub fn is_clean(&self) -> bool {
        self.touched.is_empty()
    }

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
    pub fn hash(&mut self) -> u64 {
        self.state.hash.unwrap_or_else(|| self.calculate_hash())
    }

    fn calculate_hash(&mut self) -> u64 {
        let mut s = DefaultHasher::new();

        self.dim.hash(&mut s);
        self.data.hash(&mut s);

        let hash = s.finish();
        self.state.hash = Some(hash);
        hash
    }

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

        return Equal;
    }

    pub fn subset_eq(&self, other: &Self) -> bool {
        assert_eq!(self.dim, other.dim);
        let dim = self.dim;
        let n = dim * dim - 1;

        try_subset(&self.data, &other.data, 1, n) == DBMRelation::Subset
    }

    pub fn superset_eq(&self, other: &Self) -> bool {
        assert_eq!(self.dim, other.dim);
        let dim = self.dim;
        let n = dim * dim - 1;

        try_superset(&self.data, &other.data, 1, n) == DBMRelation::Superset
    }

    pub fn eq(&self, other: &Self) -> bool {
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
    pub fn constrain(
        self,
        i: ClockIndex,
        j: ClockIndex,
        constraint: Inequality,
    ) -> Option<DBM<Dirty>> {
        self.make_dirty().constrain(i, j, constraint)
    }

    /// Constrains the DBM with `dbm[i,j]=constraint` without closing it afterwards
    pub fn constrain_raw(
        self,
        i: ClockIndex,
        j: ClockIndex,
        constraint: RawInequality,
    ) -> Option<DBM<Dirty>> {
        self.make_dirty().constrain_raw(i, j, constraint)
    }

    pub fn tighten(self, i: ClockIndex, j: ClockIndex, constraint: RawInequality) -> Self {
        debug_assert!(self[(i, j)] > constraint && constraint.as_negated() < self[(j, i)]);

        let mut dbm = self.make_unsafe();
        dbm[(i, j)] = constraint;
        dbm.close_ij(i, j).expect("Tightening must never be empty")
    }

    pub fn new(dim: ClockIndex, value: Inequality) -> DBM<Dirty> {
        assert!(dim > 0);
        DBM {
            dim,
            data: vec![value.into(); dim * dim],
            state: Dirty::dirty(dim),
        }
    }

    pub fn new_raw(dim: ClockIndex, value: RawInequality) -> DBM<Dirty> {
        assert!(dim > 0);
        DBM {
            dim,
            data: vec![value; dim * dim],
            state: Dirty::dirty(dim),
        }
    }

    pub fn zero(dim: ClockIndex) -> DBM<Valid> {
        assert!(dim > 0);
        DBM {
            dim,
            data: vec![LE_ZERO; dim * dim],
            state: Valid { hash: None },
        }
    }

    pub fn init(dim: ClockIndex) -> DBM<Valid> {
        let res = DBM::zero(dim);
        res.up()
    }

    pub fn up(self) -> Self {
        let mut dbm = self.make_unsafe();

        for i in 1..dbm.dim {
            dbm[(i, 0)] = LS_INFINITY;
        }

        unsafe { dbm.assert_valid() }
    }

    pub fn intersection(self, src: &Self) -> Option<Self> {
        assert_eq!(self.dim, src.dim);
        let dim = self.dim;

        let mut dst = self.make_dirty();

        for i in 0..dim {
            for j in 0..dim {
                if dst[(i, j)] > src[(i, j)] {
                    dst[(i, j)] = src[(i, j)];
                    if src[(i, j)].as_negated() >= dst[(i, j)] {
                        return None;
                    }
                }
            }
        }
        let res = dst.close();

        Some(res.expect("Expected non-empty DBM after close"))
    }

    pub fn intersects(&self, other: &Self) -> bool {
        assert_eq!(self.dim, other.dim);

        for i in 1..self.dim {
            for j in 0..self.dim {
                let dbm1_ij = self[(i, j)];
                if dbm1_ij != LS_INFINITY && dbm1_ij.as_negated() >= other[(j, i)] {
                    return false;
                }
                let dbm2_ij = other[(i, j)];
                if dbm2_ij != LS_INFINITY && dbm2_ij.as_negated() >= self[(j, i)] {
                    return false;
                }
            }
        }

        return true;
    }

    pub fn satisfies(&self, i: ClockIndex, j: ClockIndex, constraint: Inequality) -> bool {
        self.satisfies_raw(i, j, constraint.into())
    }

    pub fn satisfies_raw(&self, i: ClockIndex, j: ClockIndex, constraint: RawInequality) -> bool {
        assert!(i != j);
        !(self[(i, j)] > constraint && constraint.as_negated() >= self[(j, i)])
    }

    pub fn is_unbounded(&self) -> bool {
        for i in 1..self.dim {
            if self[(i, 0)] < LS_INFINITY {
                return false;
            }
        }

        return true;
    }

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

    fn make_dirty(self) -> DBM<Dirty> {
        DBM {
            dim: self.dim,
            data: self.data,
            state: Dirty::clean(self.dim),
        }
    }

    /// Tighten the dbm with the negated constraints of rhs dbm
    pub fn subtract_dbm(self, rhs: &DBM<Valid>) -> Vec<DBM<Valid>> {
        if self.intersects(rhs) {
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

    pub(super) fn internal_subtract_dbm(
        self,
        rhs: &DBM<Valid>,
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

                rhs[(i, j)] < dbm1[(i, j)]
            })
            .collect();

        let mut n_cons = indices.len();

        let mut result = vec![];

        let mut i = 0;
        let mut j = 0;
        let mut c = None;

        while n_cons > 0 {
            /*********************** find constraint i,j to subtract ***************/
            let mut bestv: RawInequality = RawInequality::MAX;
            let mut k = 0;

            while k < n_cons {
                let (ci, cj) = indices[k];

                // If dbm2 outside dbm1 then no more subtraction.
                debug_assert!(rhs[(ci, cj)] != LS_INFINITY);
                if rhs[(ci, cj)].as_negated() > dbm1[(cj, ci)] {
                    result.push(dbm1);
                    return result;
                }

                if rhs[(ci, cj)] >= dbm1[(ci, cj)] {
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
                        let cv = worst_value(&dbm1, rhs, ci, cj);

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
            n_cons -= 1;
            indices[c] = indices[n_cons]; // Swap the last

            debug_assert!(i != j);
            debug_assert!(rhs[(i, j)] != LS_INFINITY);
            /******************* Subtraction for dbm2[i,j] *********************/
            if rhs[(i, j)] < dbm1[(i, j)] {
                let neg_cons = rhs[(i, j)].as_negated();
                debug_assert!(neg_cons < dbm1[(j, i)]);
                if n_cons == 0 {
                    // is last constraint?
                    result.push(dbm1.tighten(j, i, neg_cons));
                    return result;
                }
                result.push(dbm1.clone().tighten(j, i, neg_cons));
                dbm1 = dbm1.tighten(i, j, rhs[(i, j)]) // continue with remainders
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

        debug_assert!(dbm.is_diagonal_ok_and_clocks_positive());

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
    pub fn constrain(self, i: ClockIndex, j: ClockIndex, constraint: Inequality) -> Option<Self> {
        check_indices!(self, i, j);

        self.constrain_raw(i, j, constraint.into())
    }

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

                    /* UDBM COMMENT:
                     * *MUST* be there (ideally before the loop on j)
                     * to avoid numerical problems: computation may
                     * diverge to -infinity and go beyond reasonable
                     * bounds and produce numerical errors in case of
                     * empty DBMs. This was exhibited by extensive testing.
                     * The old implementation is therefor numerically wrong.
                     * Having the test here also allows for testing non
                     * emptiness of a DBM.
                     * It is still possible to have numerical errors but
                     * it is much more difficult now.
                     */
                    if dbm[(i, i)] < LE_ZERO {
                        // the new DBM is empty
                        return None;
                    }
                }
            }
        }

        Some(unsafe { dbm.assert_valid() })
    }

    pub fn close(self) -> Option<DBM<Valid>> {
        self.close_touched()
    }

    #[allow(unused)]
    fn close_all(mut self) -> Option<DBM<Valid>> {
        let mut dbm = self.make_unsafe();

        for k in 0..dbm.dim {
            for i in 0..dbm.dim {
                /* UDBM COMMENT:
                 * optimization: if i == k
                 * the loop will tighten dbm[i,j] with dbm[i,i] + dbm[i,j]
                 * which will change nothing, even for i == j (if < 0 then
                 * more < 0, but still empty).
                 */

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
                    /* UDBM COMMENT:
                     * *MUST* be there (ideally before the loop on j)
                     * to avoid numerical problems: computation may
                     * diverge to -infinity and go beyond reasonable
                     * bounds and produce numerical errors in case of
                     * empty DBMs. This was exhibited by extensive testing.
                     * The old implementation is therefor numerically wrong.
                     * Having the test here also allows for testing non
                     * emptiness of a DBM.
                     * It is still possible to have numerical errors but
                     * it is much more difficult now.
                     */
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

        debug_assert!(dbm.is_diagonal_ok_and_clocks_positive());

        dbm
    }
}

impl DBM<Unsafe> {
    pub fn is_empty(&self) -> bool {
        for i in 0..self.dim {
            if self[(i, i)] < LE_ZERO {
                return true;
            }
        }
        false
    }

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

    /// Assert that a DBM is closed without checking (in release builds)
    ///
    /// This method is always memory safe!
    ///
    /// It is 'only' unsafe in that it can be called on an unclosed DBM
    /// which breaks the preconditions on every method which requires closed DBMs
    ///
    unsafe fn assert_valid(self) -> DBM<Valid> {
        debug_assert!(self.is_valid());

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
        //write!(f, "\n")?;
        let mut lines = vec![];

        for i in 0..self.dim {
            let mut line = vec![];

            for j in 0..self.dim {
                line.push(format!("{}", self[(i, j)]));
                //write!(f, "{} ", self[(i, j)])?;
            }
            lines.push(line);
            //write!(f, "]\n")?;
        }

        let max_len = lines.iter().flatten().map(|s| s.len()).max().unwrap();
        for line in lines {
            write!(f, "[ ")?;
            for s in line {
                write!(f, "{:<max_len$}", s)?;
            }
            write!(f, "]\n")?;
        }
        Ok(())
    }
}

#[allow(unused)]
mod test {
    use super::DBM;
    use crate::dbm::DBMRelation;
    use crate::util::bit_conversion::{u32s_to_represent_bits, u32s_to_represent_bytes};

    #[test]
    fn dbm1() {
        use super::DBM;
        use crate::util::constraints::Inequality::*;

        let dbm = DBM::new(10, LE(0));
        let dbm = dbm.close().unwrap();

        assert!(dbm.intersects(&dbm));
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

        assert!(old.intersects(&dbm));
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

        assert!(original.intersects(&dbm));
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

                assert!(!dbm1.intersects(&dbm2));

                assert!(dbm1.intersects(&dbm3));
                assert!(dbm2.intersects(&dbm3));
            }

            Some(())
        }
        test().unwrap()
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
    fn dbm_order1() {
        let zero = DBM::zero(8);
        let init = DBM::init(8);

        assert!(zero.subset_eq(&init));
        assert!(init.superset_eq(&zero));
        assert!(!zero.eq(&init));
        assert!(zero.eq(&zero));
        assert!(init.eq(&init));
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
        assert!(!zero.eq(&five));
        assert!(zero.eq(&zero));
        assert!(five.eq(&five));
        assert_eq!(zero.relation_to(&five), DBMRelation::Different);
        assert_eq!(five.relation_to(&zero), DBMRelation::Different);
    }

    #[test]
    fn bits_to_ints() {
        assert_eq!(u32s_to_represent_bits(1), 1);
        assert_eq!(u32s_to_represent_bits(32), 1);
        assert_eq!(u32s_to_represent_bits(33), 2);
        assert_eq!(u32s_to_represent_bits(65), 3);
    }

    #[test]
    fn bytes_to_ints() {
        assert_eq!(u32s_to_represent_bytes(1), 1);
        assert_eq!(u32s_to_represent_bytes(4), 1);
        assert_eq!(u32s_to_represent_bytes(5), 2);
        assert_eq!(u32s_to_represent_bytes(9), 3);
    }
}
