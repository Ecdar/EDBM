use std::{
    fmt::{Debug, Display},
    ops::{Add, AddAssign, Not},
};

use crate::{
    memory::allocator::{DBMAllocator, DBMPtr},
    util::{
        bounds::Bounds,
        constraints::{check_weak_add, Bound, ClockIndex, Disjunction, Inequality, RawInequality},
    },
};

use super::{
    minimal_graph::get_dbm_bit_matrix,
    util::{dbm_list_reduce, dbm_list_union},
    DBMRelation, Dirty, ImmutableDBM, Valid, DBM,
};

/// Shared Federations are immutable but can share memory of internal DBMs using an allocator
pub type SharedFederation = Federation<DBMPtr>;
pub type OwnedFederation = Federation<DBM<Valid>>;

/// Owned Federations are mutable. They own the internal DBMs allowing for efficient (lockless) internal mutability.
#[derive(Clone)]
pub struct Federation<T>
where
    T: ImmutableDBM,
{
    pub(crate) dim: ClockIndex,
    pub(crate) dbms: Vec<T>,
}

impl<T: ImmutableDBM> Federation<T> {
    pub fn owned_clone(&self) -> OwnedFederation {
        T::owned_fed_clone(self)
    }

    pub fn dim(&self) -> ClockIndex {
        self.dim
    }

    pub fn can_delay_indefinitely(&self) -> bool {
        self.dbms
            .iter()
            .any(|dbm| dbm.as_valid_ref().can_delay_indefinitely())
    }

    pub fn empty(dim: ClockIndex) -> Self {
        Self { dim, dbms: vec![] }
    }

    pub fn is_empty(&self) -> bool {
        self.dbms.is_empty()
    }

    pub fn is_universe(&self) -> bool {
        let uni = OwnedFederation::universe(self.dim);
        uni.subset_eq(self)
    }

    pub fn size(&self) -> usize {
        self.dbms.len()
    }

    pub fn is_unbounded(&self) -> bool {
        for dbm in &self.dbms {
            if dbm.as_valid_ref().is_unbounded() {
                return true;
            }
        }

        false
    }

    fn try_get_only_dbm(&self) -> Option<&T> {
        if self.dbms.len() == 1 {
            return self.dbms.first();
        }
        None
    }

    fn first_dbm(&self) -> &T {
        assert!(!self.is_empty());
        self.dbms.first().unwrap()
    }

    fn is_subtraction_empty<D: ImmutableDBM>(&self, other: &Federation<D>) -> bool {
        assert_eq!(self.dim, other.dim);
        if self.is_empty() {
            return true;
        } else if other.is_empty() {
            return false;
        }

        if self.subset_eq_dbm(other.first_dbm().as_valid_ref()) {
            true // If all DBMs are subset_eq, the subtraction is empty
        } else if other.size() == 1 {
            false // If it is the only DBM we know the result (!subset_eq)
        } else {
            self.owned_clone().subtraction(other).is_empty()
        }
    }

    pub fn subset_eq<D: ImmutableDBM>(&self, other: &Federation<D>) -> bool {
        self.is_subtraction_empty(other)
    }

    pub fn superset_eq<D: ImmutableDBM>(&self, other: &Federation<D>) -> bool {
        other.is_subtraction_empty(self)
    }

    pub fn subset_eq_dbm<D: ImmutableDBM>(&self, other: &D) -> bool {
        if self.is_empty() {
            return true;
        }

        for self_dbm in &self.dbms {
            if !self_dbm.as_valid_ref().subset_eq(other.as_valid_ref()) {
                return false;
            }
        }

        true
    }

    pub fn has_intersection<D: ImmutableDBM>(&self, other: &Federation<D>) -> bool {
        assert_eq!(self.dim, other.dim);
        if other.is_empty() {
            return false;
        }
        for dbm1 in &self.dbms {
            for dbm2 in &other.dbms {
                if dbm1.as_valid_ref().has_intersection(dbm2.as_valid_ref()) {
                    return true;
                }
            }
        }
        false
    }

    pub fn inverse(&self) -> OwnedFederation {
        OwnedFederation::universe(self.dim).subtraction(self)
    }

    pub fn superset_eq_dbm<D: ImmutableDBM>(&self, other: &D) -> bool {
        let other = OwnedFederation::from_dbm(other.as_valid_ref().clone());
        self.superset_eq(&other)
    }

    pub fn equals<D: ImmutableDBM>(&self, other: &Federation<D>) -> bool {
        self.relation(other) == DBMRelation::Equal
    }

    /// This is always exact (as opposed to UDBM which has an exact and inexact variant)
    pub fn relation<D: ImmutableDBM>(&self, other: &Federation<D>) -> DBMRelation {
        use DBMRelation::*;
        let self_included = self.is_subtraction_empty(other);
        let other_included = other.is_subtraction_empty(self);

        match (self_included, other_included) {
            (true, true) => Equal,
            (true, false) => Subset,
            (false, true) => Superset,
            (false, false) => Different,
        }
    }

    pub fn minimal_constraints(&self) -> Disjunction {
        let fed = self.owned_clone().merge_expensive_reduce(0);
        let mut conjunctions = Vec::with_capacity(self.size());
        for dbm in &fed.dbms {
            let conjunction = dbm.as_valid_ref().conjunction_of_minimal_constraints();
            conjunctions.push(conjunction);
        }

        Disjunction::new(conjunctions)
    }
}

impl OwnedFederation {
    pub fn from_disjunction(disjunction: &Disjunction, dim: ClockIndex) -> Self {
        let mut fed = Federation::empty(dim);
        for conj in disjunction.iter() {
            // Don't need append_dbm here as we know the DBMs are as reduced as possible
            fed.dbms.push(DBM::from_conjunction(conj, dim));
        }

        fed
    }

    /// Constrains the federation DBMs with `dbm[i,j]=constraint`.
    pub fn constrain_raw(self, i: ClockIndex, j: ClockIndex, constraint: RawInequality) -> Self {
        self.filter_map_all(|dbm| dbm.constrain_and_close_raw(i, j, constraint))
    }

    /// Constrains the federation DBMs with `dbm[i,j]=constraint`.
    pub fn constrain(self, i: ClockIndex, j: ClockIndex, constraint: Inequality) -> Self {
        self.filter_map_all(|dbm| dbm.constrain_and_close(i, j, constraint))
    }

    /// Constrains the federation DBMs such that `bound<=clock<=bound` e.g. `clock=bound`.
    pub fn constrain_eq(self, clock: ClockIndex, bound: Bound) -> Self {
        use Inequality::*;
        self.constrain(clock, 0, LE(bound)) // Lower bound
            .constrain(0, clock, LE(-bound)) // Upper bound
    }

    /// Efficient method to apply multiple constraints at once, because the DBMs are only closed once at the end.
    pub fn constrain_raw_many(
        self,
        constraints: Vec<(ClockIndex, ClockIndex, RawInequality)>,
    ) -> Self {
        self.filter_map_all_dirty(|dbm| {
            let mut res = Some(dbm);
            for (i, j, constraint) in &constraints {
                res = res?.constrain_raw(*i, *j, *constraint);
            }

            res
        })
    }

    /// Efficient method to apply multiple constraints at once, because the DBMs are only closed once at the end.
    pub fn constrain_many(self, constraints: Vec<(ClockIndex, ClockIndex, Inequality)>) -> Self {
        self.filter_map_all_dirty(|dbm| {
            let mut res = Some(dbm);
            for (i, j, constraint) in &constraints {
                res = res?.constrain(*i, *j, *constraint)
            }

            res
        })
    }

    pub fn tighten(self, i: ClockIndex, j: ClockIndex, constraint: RawInequality) -> Self {
        self.map_all(|dbm| dbm.tighten(i, j, constraint))
    }

    pub fn up(self) -> Self {
        self.map_all(|dbm| dbm.up())
    }

    pub fn down(self) -> Self {
        self.map_all(|dbm| dbm.down())
    }

    pub fn satisfies(&self, i: ClockIndex, j: ClockIndex, constraint: Inequality) -> bool {
        self.dbms.iter().any(|dbm| dbm.satisfies(i, j, constraint))
    }

    pub fn satisfies_raw(&self, i: ClockIndex, j: ClockIndex, constraint: RawInequality) -> bool {
        self.dbms
            .iter()
            .any(|dbm| dbm.satisfies_raw(i, j, constraint))
    }

    pub fn update_clock_val(self, clock: ClockIndex, val: Bound) -> Self {
        self.map_all(|dbm| dbm.update_clock_val(clock, val))
    }

    pub fn update_clock_clock(self, clock_i: ClockIndex, clock_j: ClockIndex) -> Self {
        self.map_all(|dbm| dbm.update_clock_clock(clock_i, clock_j))
    }

    pub fn update(self, i: ClockIndex, j: ClockIndex, val: Bound) -> Self {
        self.map_all(|dbm| dbm.update(i, j, val))
    }

    pub fn update_increment(self, clock: ClockIndex, inc: Bound) -> Self {
        self.map_all(|dbm| dbm.update_increment(clock, inc))
    }

    pub fn free_clock(self, clock: ClockIndex) -> Self {
        self.map_all(|dbm| dbm.free_clock(clock))
    }

    pub fn extrapolate_max_bounds(self, bounds: &Bounds) -> Self {
        self.map_all(|dbm| dbm.extrapolate_max_bounds(bounds))
    }

    pub fn extrapolate_lu_bounds(self, bounds: &Bounds) -> Self {
        self.map_all(|dbm| dbm.extrapolate_lu_bounds(bounds))
    }

    pub fn set_empty(mut self) -> Self {
        self.dbms.clear();
        self
    }

    pub fn dbm_intersection(mut self, dbm2: &DBM<Valid>) -> Self {
        let mut res = Vec::with_capacity(self.size());
        for dbm1 in self.dbms {
            if let Some(intersection) = dbm1.intersection(dbm2) {
                res.push(intersection);
            }
        }

        self.dbms = res;
        self
    }

    pub fn intersection(self, other: &Self) -> Self {
        assert_eq!(self.dim, other.dim);
        if self.is_empty() || other.is_empty() {
            return self.set_empty();
        }

        let dim = self.dim;
        let s1 = self.size();
        let s2 = other.size();

        let mut res = Vec::with_capacity(s1 * s2);
        let mut skips = res.len();
        for dbm2 in &other.dbms[1..s2] {
            res.extend(self.clone().dbm_intersection(dbm2).merge_reduce(skips).dbms);
            skips = res.len();
        }

        // Avoid final clone
        res.extend(
            self.dbm_intersection(&other.dbms[0])
                .merge_reduce(skips)
                .dbms,
        );

        Self { dim, dbms: res }
    }

    fn steal(mut self, fed: Self) -> Self {
        let size = self.size();
        self.dbms.extend(fed.dbms);
        self.merge_reduce(size)
    }

    #[must_use]
    pub fn predt(&self, bads: &Self) -> Self {
        let goods = self;
        if bads.is_empty() {
            return goods.clone().down();
        }

        if goods.is_empty() {
            return goods.clone();
        }

        let dim = goods.dim;

        let mut result = Self::empty(dim);
        for good in &goods.dbms {
            let down_good = good.clone().down();

            let bad = &bads.dbms[0]; // We know it is non-empty

            let mut intersect_predt = Self::from_dbm(down_good.clone());

            if down_good.has_intersection(bad) {
                let down_bad = Self::from_dbm(bad.clone().down());
                intersect_predt = intersect_predt
                    .subtraction(&down_bad)
                    .steal(down_bad.dbm_intersection(good).subtract_dbm(bad).down());
            }

            // Intersection with other predt
            for bad in &bads.dbms[1..] {
                if down_good.has_intersection(bad) {
                    let down_bad = Self::from_dbm(bad.clone().down());

                    let part = Self::from_dbm(down_good.clone())
                        .subtraction(&down_bad)
                        .steal(down_bad.dbm_intersection(good).subtract_dbm(bad).down());

                    intersect_predt = intersect_predt.intersection(&part);
                    if intersect_predt.is_empty() {
                        break;
                    }
                }
            }

            // Union of partial predt
            result = result.steal(intersect_predt);
        }

        result
    }

    fn filter_map_all<F>(self, f: F) -> Self
    where
        F: Fn(DBM<Valid>) -> Option<DBM<Valid>>,
    {
        Self {
            dbms: self.dbms.into_iter().filter_map(f).collect(),
            dim: self.dim,
        }
    }

    fn filter_map_all_dirty<F>(self, f: F) -> Self
    where
        F: Fn(DBM<Dirty>) -> Option<DBM<Dirty>>,
    {
        Self {
            dbms: self
                .dbms
                .into_iter()
                .map(|dbm| dbm.make_dirty())
                .filter_map(f)
                .filter_map(|dbm| dbm.close())
                .collect(),
            dim: self.dim,
        }
    }

    fn map_all<F>(self, f: F) -> Self
    where
        F: Fn(DBM<Valid>) -> DBM<Valid>,
    {
        Self {
            dbms: self.dbms.into_iter().map(f).collect(),
            dim: self.dim,
        }
    }

    pub fn from_dbm(dbm: DBM<Valid>) -> Self {
        let dim = dbm.dim;
        OwnedFederation {
            dbms: vec![dbm],
            dim,
        }
    }

    pub fn from_dbms(dim: ClockIndex, dbms: Vec<DBM<Valid>>) -> Self {
        OwnedFederation { dbms, dim }
    }

    pub fn universe(dim: ClockIndex) -> Self {
        assert!(dim > 0);

        OwnedFederation {
            dbms: vec![DBM::universe(dim)],
            dim,
        }
    }

    pub fn init(dim: ClockIndex) -> Self {
        assert!(dim > 0);

        OwnedFederation {
            dbms: vec![DBM::init(dim)],
            dim,
        }
    }

    pub fn zero(dim: ClockIndex) -> Self {
        assert!(dim > 0);

        OwnedFederation {
            dbms: vec![DBM::zero(dim)],
            dim,
        }
    }

    pub fn reduce(self) -> Self {
        OwnedFederation {
            dbms: dbm_list_reduce(self.dbms),
            dim: self.dim,
        }
    }

    pub fn expensive_reduce(mut self) -> Self {
        if self.size() < 2 {
            return self;
        }

        let mut i = 0;
        let dim = self.dim;

        while i < self.dbms.len() {
            // Take out a dbm and check whether it is a subset of the remainder
            let dbm = self.dbms.swap_remove(i);

            // self <= dbm
            if self.subset_eq_dbm(&dbm) {
                // this dbm contains the entire remainder,
                // so the federation can be replaced by it alone
                return Self {
                    dbms: vec![dbm],
                    dim,
                };
            } else {
                let mut dbm_fed = Self::from_dbm(dbm);
                // dbm <= self
                if self.superset_eq(&dbm_fed) {
                    // this remainder contains the dbm,
                    // so the dbm can be dropped from the federation
                    drop(dbm_fed);
                } else {
                    // The dbm is incomparable to the remainder
                    // Put it back
                    // We know there is only one DBM so we can move it
                    self.dbms.insert(0, dbm_fed.dbms.pop().unwrap());
                    i += 1;
                }
            }
        }

        self
    }

    pub fn merge_expensive_reduce(self, skips: usize) -> Self {
        self.merge_reduce_internal(true, skips)
    }

    pub fn merge_reduce(self, skips: usize) -> Self {
        self.merge_reduce_internal(false, skips)
    }

    fn merge_reduce_internal(mut self, expensive: bool, skips: usize) -> Self {
        let mut i = skips;
        let dim = self.dim;

        'i: while i < self.size() {
            let mut j = 0;
            'j: while i < self.size() && j != i {
                // j < i
                let dbm_i = &self.dbms[i];
                let dbm_j = &self.dbms[j];

                let mut nb_ok = if dim <= 2 { 1 } else { 0 };

                let mut subset = true;
                let mut superset = true;

                for k in 1..dim {
                    let mut cons_ok = false;
                    for l in 0..k {
                        let ij = (k, l);
                        let ji = (l, k);

                        if check_weak_add(dbm_i[ij], dbm_j[ji])
                            || check_weak_add(dbm_i[ji], dbm_j[ij])
                        {
                            // Next j
                            j += 1;
                            continue 'j;
                        }

                        subset &= dbm_i[ij] <= dbm_j[ij];
                        superset &= dbm_i[ij] >= dbm_j[ij];
                        subset &= dbm_i[ji] <= dbm_j[ji];
                        superset &= dbm_i[ji] >= dbm_j[ji];

                        cons_ok |= dbm_i[ij] == dbm_j[ij] && dbm_i[ji] == dbm_j[ji];
                    }
                    if cons_ok {
                        nb_ok += 1;
                    }
                }

                if subset {
                    //Remove dbm_i
                    self.dbms.swap_remove(i);
                    continue 'i;
                } else if superset {
                    // Remove dbm_j
                    self.dbms.remove(j); // Can't swap remove here because order matters
                    assert!(i > 0);
                    i -= 1;
                    continue 'j;
                } else if nb_ok > 0 {
                    let cu = dbm_i.clone().convex_union(dbm_j);
                    let cu_fed = Self::from_dbm(cu.clone());
                    let mut remainder = cu_fed.subtract_dbm(dbm_i);

                    let mut safe_merge = remainder.subset_eq_dbm(dbm_j);
                    if !safe_merge {
                        remainder = remainder.subtract_dbm(dbm_i);
                        assert!(!remainder.is_empty());

                        if expensive {
                            // See if (convex union)-(dbmi|dbmj) is included somewhere.
                            for k in 0..self.size() {
                                if k != i && k != j {
                                    remainder = remainder.subtract_dbm(&self.dbms[k]);
                                    if remainder.is_empty() {
                                        safe_merge = true;
                                        break;
                                    }
                                }
                            }
                        } else {
                            // Remove incrementally DBMs from (convex union)-(dbmi|dbmj)
                            // and check if the remaining becomes empty.
                            for k in 0..self.size() {
                                if k != i && k != j {
                                    remainder.remove_included_in_dbm(&self.dbms[k]);
                                    if remainder.is_empty() {
                                        safe_merge = true;
                                        break;
                                    }
                                }
                            }
                        }
                    }

                    assert!(j < i);
                    if safe_merge {
                        self.dbms.swap_remove(i);
                        self.dbms[j] = cu;
                    } else {
                        j += 1;
                    }
                } else {
                    j += 1;
                }
            }
            i += 1;
        }

        //println!("Done");
        self
    }

    fn subtract_dbm<D: ImmutableDBM>(self, other: &D) -> Self {
        if self.is_empty() {
            return self;
        }

        let mut mingraph = None;

        let mut result = Vec::with_capacity(2 * self.size());
        let dim = self.dim;

        let other = other.as_valid_ref();
        for dbm in self.dbms {
            if dbm.maybe_intersects(other) {
                let mingraph = mingraph.get_or_insert_with(|| get_dbm_bit_matrix(other));
                if mingraph.n_cons == 0 {
                    // That means we remove everything.
                    return OwnedFederation::empty(dim);
                }
                let partial = dbm.internal_subtract_dbm(other, mingraph);
                result = dbm_list_union(result, partial);
            } else {
                result.push(dbm);
            }
        }

        Self { dbms: result, dim }
    }

    pub fn append_dbm(&mut self, dbm: DBM<Valid>) {
        self.dbms.push(dbm);
    }

    /// Non-convex union of the federations consuming the DBMs in `other` to append to `self`'s DBMs
    pub fn union<D: ImmutableDBM>(mut self, other: &Federation<D>) -> Self {
        if self.is_empty() {
            return other.owned_clone();
        }

        for dbm in &other.dbms {
            let dbm = dbm.as_valid_ref();
            if self.remove_included_in_dbm(dbm) {
                self.append_dbm(dbm.clone());
            }
        }

        self
    }

    fn remove_included_in_dbm(&mut self, dbm: &DBM<Valid>) -> bool {
        let mut other_not_included = true;

        let mut i = 0;
        while i < self.size() {
            match self.dbms[i].relation_to(dbm) {
                DBMRelation::Subset | DBMRelation::Equal => {
                    self.dbms.swap_remove(i);
                }
                DBMRelation::Superset => {
                    other_not_included = false;
                    i += 1;
                }
                DBMRelation::Different => i += 1,
            };
        }

        other_not_included
    }

    pub fn subtraction<D: ImmutableDBM>(self, other: &Federation<D>) -> Self {
        let mut res = self;

        if let Some(dbm) = other.try_get_only_dbm() {
            return res.subtract_dbm(dbm);
        } else if !res.is_empty() && !other.is_empty() {
            // Otherwise the subtraction does nothing
            for dbm in &other.dbms {
                res = res.subtract_dbm(dbm);

                if res.is_empty() {
                    break;
                }
            }
        }

        res
    }

    pub(crate) fn get_dbm(&self, index: usize) -> Option<DBM<Valid>> {
        self.dbms.get(index).cloned()
    }

    pub fn into_shared(self, alloc: impl DBMAllocator) -> SharedFederation {
        SharedFederation {
            dbms: self.dbms.into_iter().map(|dbm| alloc.to_ptr(dbm)).collect(),
            dim: self.dim,
        }
    }
}

impl Add for OwnedFederation {
    type Output = Self;

    fn add(mut self, other: Self) -> Self {
        if self.is_empty() {
            return other;
        }

        for dbm in other.dbms {
            if self.remove_included_in_dbm(&dbm) {
                self.append_dbm(dbm);
            }
        }

        self
    }
}

impl AddAssign for OwnedFederation {
    fn add_assign(&mut self, other: Self) {
        *self = other.union(self);
    }
}

impl Not for OwnedFederation {
    type Output = Self;

    /// Get a federation containing the inverse of the federation
    fn not(self) -> Self {
        self.inverse()
    }
}

impl<D: ImmutableDBM> Display for Federation<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.minimal_constraints().fmt(f)
    }
}

impl<D: ImmutableDBM> Debug for Federation<D> {
    // Same as Display
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Federation{{")?;
        for (i, dbm) in self.dbms.iter().enumerate() {
            writeln!(
                f,
                "{}",
                format!("  DBM {}:\n{}", i + 1, dbm.as_valid_ref())
                    .strip_suffix('\n')
                    .unwrap()
                    .replace('\n', "\n    ")
            )?;
        }

        writeln!(f, "}}")
    }
}

impl SharedFederation {
    pub fn into_owned(self) -> OwnedFederation {
        OwnedFederation {
            dbms: self.dbms.into_iter().map(|ptr| ptr.take_dbm()).collect(),
            dim: self.dim,
        }
    }
}

#[allow(unused)]
mod test {
    use rand::Rng;

    use crate::{
        util::{bounds::Bounds, constraints::Inequality},
        zones::{
            rand_gen::{random_dbm_in_fed, random_dbm_subset, random_fed, random_fed_arg},
            DBMRelation, DBM,
        },
    };

    use super::OwnedFederation;

    const TEST_ATTEMPTS: usize = 250;
    const TEST_SIZE: usize = 10;
    const DIMS: &[usize] = &[1, 2, 5];

    #[test]
    fn rand_equals_test() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    let fed = random_fed(dim, size);

                    assert!(fed.equals(&fed));
                }
            }
        }
    }

    #[test]
    fn rand_reduce_test() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    let fed = random_fed(dim, size);

                    let reduced = fed.clone().reduce();

                    assert!(fed.equals(&reduced));
                }
            }
        }
    }

    #[test]
    fn rand_expensive_reduce_test() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    let fed = random_fed(dim, size);

                    let reduced = fed.clone().expensive_reduce();

                    assert!(fed.equals(&reduced));
                }
            }
        }
    }

    #[test]
    fn rand_merge_reduce_test() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    let fed = random_fed(dim, size);

                    let reduced = fed.clone().merge_reduce(0);

                    assert!(fed.equals(&reduced));
                }
            }
        }
    }

    #[test]
    fn rand_merge_expensive_reduce_test() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    let fed = random_fed(dim, size);

                    let reduced = fed.clone().merge_expensive_reduce(0);

                    assert!(fed.equals(&reduced));
                }
            }
        }
    }

    #[test]
    fn rand_inverse_subtract_test() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    let fed = random_fed(dim, size);

                    let inverse = fed.clone().inverse();
                    let fed2 = fed.clone().subtraction(&inverse);

                    assert!(fed.equals(&fed2));
                }
            }
        }
    }

    #[test]
    fn test_intersection() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    let fed1 = random_fed(dim, size);
                    let fed2 = random_fed_arg(&fed1, size);

                    let fed3 = fed1.clone().intersection(&fed2);
                    let dbm2_opt = fed2.get_dbm(0);

                    let fed4 = if let Some(dbm2) = &dbm2_opt {
                        fed1.clone().dbm_intersection(dbm2)
                    } else {
                        OwnedFederation::empty(dim)
                    };
                    let fed12 = fed1.clone().intersection(&fed2);
                    let fed21 = fed2.clone().intersection(&fed1);
                    assert!(fed12.equals(&fed21));
                    assert!(fed3.subset_eq(&fed1) && fed3.subset_eq(&fed2));
                    assert!(fed4.subset_eq(&fed1));
                    if let Some(dbm2) = &dbm2_opt {
                        assert!(fed4.subset_eq_dbm(dbm2));
                    }
                    for dbm3 in &fed3.dbms {
                        assert!(fed1.superset_eq_dbm(dbm3));
                        assert!(fed2.superset_eq_dbm(dbm3));
                    }

                    for dbm4 in &fed4.dbms {
                        assert!(fed1.superset_eq_dbm(dbm4));
                        if let Some(dbm2) = &dbm2_opt {
                            assert!(dbm2.superset_eq(dbm4));
                        }
                    }

                    // UDBM also checks for point inclusion here...
                }
            }
        }
    }

    #[test]
    fn test_union() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    let fed1 = random_fed(dim, size);
                    let fed2 = random_fed(dim, size);
                    let mut fed3 = fed1.clone();

                    let fed1 = fed1.union(&fed2);
                    let u_fed1 = fed1.clone().union(&fed2);

                    assert_eq!(fed1.size(), u_fed1.size());
                    assert!(fed1.equals(&u_fed1));

                    assert!(fed2.subset_eq(&fed1) && fed1.superset_eq(&fed2));

                    for dbm2 in &fed2.dbms {
                        assert!(fed1.superset_eq_dbm(dbm2));
                        fed3 = fed3.union(&OwnedFederation::from_dbm(dbm2.clone()));
                    }

                    assert!(fed1.equals(&fed3) && fed1.superset_eq(&fed3) && fed1.subset_eq(&fed3));
                    let fed1 = fed1.set_empty();
                    let fed1 = fed1.union(&fed2);
                    assert!(
                        fed1.equals(&fed2)
                            && fed1.superset_eq(&fed2)
                            && fed1.subset_eq(&fed2)
                            && fed2.equals(&fed1)
                    );
                }
            }
        }
    }

    #[test]
    fn test_up() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    let fed1 = random_fed(dim, size);
                    let fed2 = fed1.clone();
                    let fed1 = fed1.up();
                    assert!(fed2.subset_eq(&fed1));
                    assert!(size == 0 || fed1.is_unbounded());

                    let mut dbms = vec![];
                    for dbm2 in fed2.dbms {
                        dbms.push(dbm2.up());
                    }
                    let fed2 = OwnedFederation::from_dbms(dim, dbms);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed1 = fed1.reduce();
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed2 = fed2.merge_expensive_reduce(0);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    assert!(
                        fed1.clone().subtraction(&fed2).is_empty()
                            && fed2.subtraction(&fed1).is_empty()
                    );
                }
            }
        }
    }
    #[test]
    fn test_down() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    let fed1 = random_fed(dim, size);
                    let fed2 = fed1.clone();
                    let fed1 = fed1.down();
                    assert!(fed2.subset_eq(&fed1));

                    let mut dbms = vec![];
                    for dbm2 in fed2.dbms {
                        dbms.push(dbm2.down());
                    }
                    let fed2 = OwnedFederation::from_dbms(dim, dbms);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed1 = fed1.reduce();
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed2 = fed2.merge_expensive_reduce(0);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    assert!(
                        fed1.clone().subtraction(&fed2).is_empty()
                            && fed2.subtraction(&fed1).is_empty()
                    );
                }
            }
        }
    }

    #[test]
    fn test_free_clock() {
        let mut rng = rand::thread_rng();
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    if dim == 1 {
                        continue;
                    }
                    let fed1 = random_fed(dim, size);
                    let fed2 = fed1.clone();
                    let c = rng.gen_range(1..dim);
                    let fed1 = fed1.free_clock(c);
                    assert!(fed2.subset_eq(&fed1));

                    let mut dbms = vec![];
                    for dbm2 in fed2.dbms {
                        dbms.push(dbm2.free_clock(c));
                    }
                    let fed2 = OwnedFederation::from_dbms(dim, dbms);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed1 = fed1.reduce();
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed2 = fed2.merge_expensive_reduce(0);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    assert!(
                        fed1.clone().subtraction(&fed2).is_empty()
                            && fed2.subtraction(&fed1).is_empty()
                    );
                }
            }
        }
    }

    #[test]
    fn test_update_clock_val() {
        let mut rng = rand::thread_rng();
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    if dim == 1 {
                        continue;
                    }
                    let fed1 = random_fed(dim, size);
                    let fed2 = fed1.clone();
                    let c = rng.gen_range(1..dim);
                    let v = rng.gen_range(0..100);
                    let fed1 = fed1.update_clock_val(c, v);

                    let mut dbms = vec![];
                    for dbm2 in fed2.dbms {
                        dbms.push(dbm2.update_clock_val(c, v));
                    }
                    let fed2 = OwnedFederation::from_dbms(dim, dbms);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed1 = fed1.reduce();
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed2 = fed2.merge_expensive_reduce(0);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    assert!(
                        fed1.clone().subtraction(&fed2).is_empty()
                            && fed2.subtraction(&fed1).is_empty()
                    );
                }
            }
        }
    }

    #[test]
    fn test_update_clock_clock() {
        let mut rng = rand::thread_rng();
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    if dim == 1 {
                        continue;
                    }
                    let fed1 = random_fed(dim, size);
                    let fed2 = fed1.clone();
                    let c1 = rng.gen_range(1..dim);
                    let c2 = rng.gen_range(1..dim);
                    let fed1 = fed1.update_clock_clock(c1, c2);

                    let mut dbms = vec![];
                    for dbm2 in fed2.dbms {
                        dbms.push(dbm2.update_clock_clock(c1, c2));
                    }
                    let fed2 = OwnedFederation::from_dbms(dim, dbms);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed1 = fed1.reduce();
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed2 = fed2.merge_expensive_reduce(0);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    assert!(
                        fed1.clone().subtraction(&fed2).is_empty()
                            && fed2.subtraction(&fed1).is_empty()
                    );
                }
            }
        }
    }

    #[test]
    fn test_update_increment() {
        let mut rng = rand::thread_rng();
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    if dim == 1 {
                        continue;
                    }
                    let fed1 = random_fed(dim, size);
                    let fed2 = fed1.clone();
                    let c1 = rng.gen_range(1..dim);
                    let v = rng.gen_range(0..50);

                    let fed1 = fed1.update_increment(c1, v);

                    let mut dbms = vec![];
                    for dbm2 in fed2.dbms {
                        dbms.push(dbm2.update_increment(c1, v));
                    }
                    let fed2 = OwnedFederation::from_dbms(dim, dbms);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed1 = fed1.reduce();
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed2 = fed2.merge_expensive_reduce(0);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    assert!(
                        fed1.clone().subtraction(&fed2).is_empty()
                            && fed2.subtraction(&fed1).is_empty()
                    );
                }
            }
        }
    }

    #[test]
    fn test_update() {
        let mut rng = rand::thread_rng();
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 0..TEST_SIZE {
                    if dim == 1 {
                        continue;
                    }
                    let fed1 = random_fed(dim, size);
                    let fed2 = fed1.clone();
                    let c1 = rng.gen_range(1..dim);
                    let c2 = rng.gen_range(1..dim);

                    let v = rng.gen_range(0..100);

                    let fed1 = fed1.update(c1, c2, v);

                    let mut dbms = vec![];
                    for dbm2 in fed2.dbms {
                        dbms.push(dbm2.update(c1, c2, v));
                    }
                    let fed2 = OwnedFederation::from_dbms(dim, dbms);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed1 = fed1.reduce();
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    let fed2 = fed2.merge_expensive_reduce(0);
                    assert!(fed1.equals(&fed2) && fed2.equals(&fed1));
                    assert!(
                        fed1.clone().subtraction(&fed2).is_empty()
                            && fed2.subtraction(&fed1).is_empty()
                    );
                }
            }
        }
    }

    #[test]
    fn test_relation() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 1..TEST_SIZE {
                    let fed = random_fed(dim, size);
                    let fed = fed.reduce();

                    let (dbm, strict) = random_dbm_subset(random_dbm_in_fed(&fed));
                    assert!(fed.superset_eq_dbm(&dbm));
                    if strict {
                        let fed2 = OwnedFederation::from_dbm(dbm.clone());
                        assert!(fed.relation(&fed2) == DBMRelation::Superset);
                        assert!(fed2.relation(&fed) == DBMRelation::Subset);
                    }
                }
            }
        }
    }

    #[test]
    fn test_subtract() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 1..TEST_SIZE {
                    let fed1 = random_fed(dim, size);
                    let fed2 = random_fed_arg(&fed1, size);
                    let mut fed3 = fed1.clone();
                    let fed4 = fed1.clone().intersection(&fed2);
                    // assert(fed4.le(fed1) && fed4.le(fed2));
                    assert!(fed4.subset_eq(&fed1) && fed4.subset_eq(&fed2));
                    assert!(fed4.clone().subtraction(&fed1).is_empty());
                    assert!(fed4.clone().subtraction(&fed2).is_empty());
                    let s12 = fed1.clone().subtraction(&fed2);
                    let s14 = fed1.clone().subtraction(&fed4);
                    assert!(s12.equals(&s14));
                    let s21 = fed2.clone().subtraction(&fed1);
                    let s24 = fed2.clone().subtraction(&fed4);
                    assert!(s21.equals(&s24));
                    let u1 = fed1.clone().union(&fed2);
                    let u2 = s12.clone().union(&s21).union(&fed4);
                    assert!(u1.equals(&u2));
                    drop(s12);
                    drop(s14);
                    drop(s21);
                    drop(s24);
                    drop(u1);
                    drop(u2);

                    let fed1 = fed1.subtraction(&fed2);

                    for dbm in &fed2.dbms {
                        fed3 = fed3.subtract_dbm(dbm);
                    }

                    assert!(fed1.equals(&fed3));
                    fed3 = fed3.merge_expensive_reduce(0);
                    assert!(fed1.equals(&fed3));
                }
            }
        }
    }

    #[test]
    fn test_predt() {
        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 1..TEST_SIZE {
                    let good = random_fed(dim, size);
                    let bad = random_fed_arg(&good, size);
                    let p = good.predt(&bad);
                    assert!(p.clone().intersection(&bad).is_empty());
                    assert!(good.subset_eq(&bad) || !(p.clone().intersection(&good)).is_empty());
                    let good_down = good.down();
                    assert!(p.subset_eq(&good_down.clone().subtraction(&bad)));
                    assert!(!bad.is_empty() || p.equals(&good_down));
                }
            }
        }
    }

    #[test]
    fn test_extrapolate() {
        let mut rng = rand::thread_rng();

        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 1..TEST_SIZE {
                    let mut bounds = Bounds::new(dim);
                    for i in 1..dim {
                        let low = rng.gen_range(-500..500);
                        let up = rng.gen_range(-500..500);
                        if low >= 0 {
                            bounds.add_lower(i, low);
                        }
                        if up >= 0 {
                            bounds.add_upper(i, up);
                        }
                    }

                    // Set lower and upper to max of upper and lower
                    let max_bounds = bounds.clone().set_to_maxes();

                    let fed1 = random_fed(dim, size);

                    let fed2 = fed1.clone().extrapolate_max_bounds(&bounds);
                    let fed3 = fed1.clone().extrapolate_lu_bounds(&max_bounds);
                    let fed4 = fed1.clone().extrapolate_lu_bounds(&bounds);

                    /// 1 <= 2 == 3 <= 4
                    assert!(fed1.subset_eq(&fed2));
                    assert!(fed2.equals(&fed3));
                    assert_eq!(fed2.relation(&fed3), DBMRelation::Equal);

                    assert!(
                        fed3.subset_eq(&fed4),
                        "max_extrap: \n{}, \nlu_extrap: \n{},\n{:?}",
                        fed2,
                        fed4,
                        bounds
                    );
                }
            }
        }
    }

    #[test]
    fn from_constraints_test() {
        let mut rng = rand::thread_rng();

        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 1..TEST_SIZE {
                    let fed1 = random_fed(dim, size);
                    let disj = fed1.minimal_constraints();
                    let fed2 = OwnedFederation::from_disjunction(&disj, dim);

                    assert!(fed1.equals(&fed2));
                }
            }
        }
    }
}
