use std::fmt::Display;

use crate::{
    memory::allocator::{DBMAllocator, DBMPtr},
    util::constraints::ClockIndex,
};

use super::{
    minimal_graph::get_dbm_bit_matrix,
    util::{dbm_list_reduce, dbm_list_union},
    DBMRelation, Valid, DBM,
};

/// Shared Federations are immutable but can share memory of internal DBMs using an allocator
#[derive(Clone)]
pub struct SharedFederation {
    dbms: Vec<DBMPtr>,
}

/// Owned Federations are mutable. They own the internal DBMs allowing for efficient (lockless) internal mutability.
#[derive(Clone)]
pub struct OwnedFederation {
    dbms: Vec<DBM<Valid>>,
}

impl OwnedFederation {
    const EMPTY: Self = OwnedFederation { dbms: vec![] };

    pub fn is_empty(&self) -> bool {
        self.dbms.is_empty()
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

    pub fn from_dbms(dbms: Vec<DBM<Valid>>) -> Self {
        OwnedFederation { dbms }
    }

    pub fn init(dim: ClockIndex) -> Self {
        assert!(dim > 0);

        OwnedFederation {
            dbms: vec![DBM::init(dim)],
        }
    }

    pub fn inverse(&self, dim: ClockIndex) -> Self {
        Self::init(dim).subtract(self)
    }

    pub fn zero(dim: ClockIndex) -> Self {
        assert!(dim > 0);

        OwnedFederation {
            dbms: vec![DBM::zero(dim)],
        }
    }

    pub fn reduce(self) -> Self {
        OwnedFederation {
            dbms: dbm_list_reduce(self.dbms),
        }
    }

    pub fn expensive_reduce(mut self) -> Self {
        if self.size() < 2 {
            return self;
        }

        let mut i = 0;

        while i < self.dbms.len() {
            // Take out a dbm and check whether it is a subset of the remainder
            let dbm = self.dbms.swap_remove(i);

            // self <= dbm
            if self.subset_eq_dbm(&dbm) {
                // this dbm contains the entire remainder,
                // so the federation can be replaced by it alone
                return Self { dbms: vec![dbm] };
            } else {
                let mut dbm_fed = Self::from_dbms(vec![dbm]);
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

    fn subtract_dbm(self, other: &DBM<Valid>) -> Self {
        if self.is_empty() {
            return self;
        }

        let mut mingraph = None;

        let mut result = vec![];

        for dbm in self.dbms {
            if dbm.intersects(other) {
                let mingraph = mingraph.get_or_insert_with(|| get_dbm_bit_matrix(other));
                if mingraph.n_cons == 0 {
                    // That means we remove everything.
                    return OwnedFederation::EMPTY;
                }
                let partial = dbm.internal_subtract_dbm(other, mingraph);
                result = dbm_list_union(result, partial);
            } else {
                result.push(dbm);
            }
        }

        Self { dbms: result }
    }

    pub fn append_dbm(mut self, dbm: &DBM<Valid>) -> Self {
        self.dbms.push(dbm.clone());
        self
    }

    pub fn append(mut self, other: &Self) -> Self {
        self.dbms.append(&mut other.dbms.clone());
        self
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

    pub fn equals(&self, other: &Self) -> bool {
        self.relation(other) == DBMRelation::Equal
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
