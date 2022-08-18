use std::fmt::Display;

use crate::{
    memory::allocator::{DBMAllocator, DBMPtr},
    util::{
        bounds::Bounds,
        constraints::{check_weak_add, Bound, ClockIndex, Inequality, RawInequality},
    },
};

use super::{
    minimal_graph::get_dbm_bit_matrix,
    util::{dbm_list_reduce, dbm_list_union},
    DBMRelation, Dirty, Valid, DBM,
};

/// Shared Federations are immutable but can share memory of internal DBMs using an allocator
#[derive(Clone)]
pub struct SharedFederation {
    pub dim: ClockIndex,
    dbms: Vec<DBMPtr>,
}

/// Owned Federations are mutable. They own the internal DBMs allowing for efficient (lockless) internal mutability.
#[derive(Clone)]
pub struct OwnedFederation {
    pub dim: ClockIndex,
    dbms: Vec<DBM<Valid>>,
}

impl OwnedFederation {
    pub fn empty(dim: ClockIndex) -> OwnedFederation {
        OwnedFederation { dim, dbms: vec![] }
    }
    pub fn is_empty(&self) -> bool {
        self.dbms.is_empty()
    }

    pub fn is_unbounded(&self) -> bool {
        for dbm in &self.dbms {
            if dbm.is_unbounded() {
                return true;
            }
        }

        false
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
        let mut res = vec![];
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

            if down_good.intersects(bad) {
                let down_bad = Self::from_dbm(bad.clone().down());
                intersect_predt = intersect_predt
                    .subtract(&down_bad)
                    .steal(down_bad.dbm_intersection(good).subtract_dbm(bad).down());
            }

            // Intersection with other predt
            for bad in &bads.dbms[1..] {
                if down_good.intersects(bad) {
                    let down_bad = Self::from_dbm(bad.clone().down());

                    let part = Self::from_dbm(down_good.clone())
                        .subtract(&down_bad)
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

    pub fn size(&self) -> usize {
        self.dbms.len()
    }

    fn try_get_only_dbm(&self) -> Option<&DBM<Valid>> {
        if self.dbms.len() == 1 {
            return self.dbms.first();
        }
        None
    }

    fn first_dbm(&self) -> &DBM<Valid> {
        assert!(!self.is_empty());
        self.dbms.first().unwrap()
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
                //println!("i={} j={}", i, j);
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

    pub fn inverse(&self) -> Self {
        Self::universe(self.dim).subtract(self)
    }

    fn subtract_dbm(self, other: &DBM<Valid>) -> Self {
        if self.is_empty() {
            return self;
        }

        let mut mingraph = None;

        let mut result = Vec::with_capacity(2 * self.size());
        let dim = self.dim;

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
    pub fn union(mut self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        for dbm in &other.dbms {
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

    pub fn subtract(self, other: &Self) -> Self {
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

    fn is_subtraction_empty(&self, other: &OwnedFederation) -> bool {
        if self.is_empty() {
            return true;
        } else if other.is_empty() {
            return false;
        }

        if self.subset_eq_dbm(other.first_dbm()) {
            true // If all DBMs are subset_eq, the subtraction is empty
        } else if other.size() == 1 {
            false // If it is the only DBM we know the result (!subset_eq)
        } else {
            self.clone().subtract(other).is_empty()
        }
    }

    pub fn subset_eq(&self, other: &Self) -> bool {
        self.is_subtraction_empty(other)
    }

    pub fn superset_eq(&self, other: &Self) -> bool {
        other.is_subtraction_empty(self)
    }

    pub fn subset_eq_dbm(&self, other: &DBM<Valid>) -> bool {
        if self.is_empty() {
            return true;
        }

        for self_dbm in &self.dbms {
            if !self_dbm.subset_eq(other) {
                return false;
            }
        }

        true
    }

    pub fn superset_eq_dbm(&self, other: &DBM<Valid>) -> bool {
        let other = Self::from_dbm(other.clone());
        self.superset_eq(&other)
    }

    pub fn equals(&self, other: &Self) -> bool {
        self.relation(other) == DBMRelation::Equal
    }

    pub(crate) fn get_dbm(&self, index: usize) -> Option<DBM<Valid>> {
        self.dbms.get(index).cloned()
    }

    /// This is always exact (as opposed to UDBM which has an exact and inexact variant)
    pub fn relation(&self, other: &Self) -> DBMRelation {
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

    pub fn into_shared(self, alloc: impl DBMAllocator) -> SharedFederation {
        SharedFederation {
            dbms: self.dbms.into_iter().map(|dbm| alloc.to_ptr(dbm)).collect(),
            dim: self.dim,
        }
    }
}

impl Display for OwnedFederation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Federation{{")?;
        for (i, dbm) in self.dbms.iter().enumerate() {
            writeln!(
                f,
                "{}",
                format!("  DBM {}:\n{}", i + 1, dbm)
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
        }
    }

    pub fn owned_clone(&self) -> OwnedFederation {
        OwnedFederation {
            dbms: self.dbms.iter().map(|ptr| ptr.clone_dbm()).collect(),
        }
    }
}

#[allow(unused)]
mod test {
    use crate::{
        util::constraints::Inequality,
        zones::{DBMRelation, DBM},
    };

    use super::OwnedFederation;

    #[test]
    fn test_relation1() {
        use Inequality::*;
        let init = DBM::init(5);
        let dbm1 = init.clone().constrain_and_close(1, 0, LE(5)).unwrap();
        let dbm2 = init.clone().constrain_and_close(0, 1, LE(-5)).unwrap();
        let fed = OwnedFederation::from_dbms(vec![dbm1, dbm2]);

        assert!(fed.subset_eq_dbm(&init));
        assert!(fed.subset_eq_dbm(&init));
    }

    #[test]
    fn test_relation2() {
        use Inequality::*;
        let init = DBM::init(5);
        let dbm1 = init.clone().constrain_and_close(1, 0, LE(5)).unwrap();
        let fed = OwnedFederation::from_dbms(vec![dbm1.clone(), dbm1]);

        assert!(fed.subset_eq_dbm(&init));
    }

    #[test]
    fn subtract_test() {
        use Inequality::*;

        let fed = OwnedFederation::init(4);
        let dbm = DBM::init(4)
            .constrain_and_close(1, 0, LE(5))
            .unwrap()
            .constrain_and_close(0, 1, LE(-5))
            .unwrap();

        let res = fed.clone().subtract_dbm(&dbm);

        println!("{fed}");
        println!("minus");
        println!("{dbm}");
        println!("=");
        println!("{res}");

        //assert!(false);
    }
    #[test]
    fn subtract_fed_test() {
        use Inequality::*;

        let fed1 = OwnedFederation::init(4);

        assert!(fed1.equals(&fed1));

        let dbm = DBM::init(4)
            .constrain_and_close(1, 0, LE(5))
            .unwrap()
            .constrain_and_close(0, 1, LE(-5))
            .unwrap();
        let fed2 = OwnedFederation::from_dbms(vec![dbm]);

        let res = fed1.clone().subtract(&fed2);

        let res2 = fed1.clone().subtract(&res);

        println!("res1: {res}");
        println!("res2: {res2}");

        assert!(res.equals(&res));
        assert!(res2.equals(&res2));

        let kinda_init = res.append(&res2);

        assert!(kinda_init.equals(&fed1));

        let before_reduce = kinda_init.append(&fed1);
        println!("Before: {before_reduce}");

        let after_reduce = before_reduce.expensive_reduce();
        println!("After: {after_reduce}");

        assert_eq!(after_reduce.size(), 1);

        assert!(after_reduce.equals(&fed1));
    }
}
