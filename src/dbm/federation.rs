use std::fmt::Display;

use crate::{
    memory::allocator::{DBMAllocator, DBMPtr},
    util::constraints::ClockIndex,
};

use super::{minimal_graph::get_dbm_bit_matrix, util::dbm_list_union, DBMRelation, Valid, DBM};

#[derive(Clone)]
pub struct SharedFederation {
    dbms: Vec<DBMPtr>,
}

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

    pub fn from_dbms(dbms: Vec<DBM<Valid>>) -> Option<Self> {
        Some(OwnedFederation { dbms })
    }

    pub fn init(dim: ClockIndex) -> Self {
        assert!(dim > 0);

        OwnedFederation {
            dbms: vec![DBM::init(dim)],
        }
    }

    pub fn inverse(&self, dim: ClockIndex) -> Self {
        Self::init(dim).subtract(&self)
    }

    pub fn zero(dim: ClockIndex) -> Self {
        assert!(dim > 0);

        OwnedFederation {
            dbms: vec![DBM::zero(dim)],
        }
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
                let partial = dbm.internal_subtract_dbm(other, &mingraph);
                result = dbm_list_union(result, partial);
            } else {
                result.push(dbm);
            }
        }

        Self { dbms: result }
    }

    pub fn add_dbm(mut self, dbm: &DBM<Valid>) -> Self {
        self.dbms.push(dbm.clone());
        self
    }

    pub fn add(mut self, other: &Self) -> Self {
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
            return true; // If all DBMs are subset_eq, the subtraction is empty
        } else if other.size() == 1 {
            return false; // If it is the only DBM we know the result (!subset_eq)
        } else {
            return self.clone().subtract(other).is_empty();
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

    pub fn eq(&self, other: &Self) -> bool {
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

    pub fn to_shared(self, alloc: impl DBMAllocator) -> SharedFederation {
        SharedFederation {
            dbms: self.dbms.into_iter().map(|dbm| alloc.to_ptr(dbm)).collect(),
        }
    }
}

impl SharedFederation {
    pub fn to_owned(self) -> OwnedFederation {
        OwnedFederation {
            dbms: self.dbms.into_iter().map(|ptr| ptr.take_dbm()).collect(),
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
                    .strip_suffix("\n")
                    .unwrap()
                    .replace("\n", "\n    ")
            )?;
        }

        writeln!(f, "}}")
    }
}

#[allow(unused)]
mod test {
    use crate::{
        dbm::{DBMRelation, DBM},
        util::constraints::Inequality,
    };

    use super::OwnedFederation;

    #[test]
    fn test_relation1() {
        use Inequality::*;
        let init = DBM::init(5);
        let dbm1 = init.clone().constrain_and_close(1, 0, LE(5)).unwrap();
        let dbm2 = init.clone().constrain_and_close(0, 1, LE(-5)).unwrap();
        let fed = OwnedFederation::from_dbms(vec![dbm1, dbm2]).unwrap();

        assert!(fed.subset_eq_dbm(&init));
        assert!(fed.subset_eq_dbm(&init));
    }

    #[test]
    fn test_relation2() {
        use Inequality::*;
        let init = DBM::init(5);
        let dbm1 = init.clone().constrain_and_close(1, 0, LE(5)).unwrap();
        let fed = OwnedFederation::from_dbms(vec![dbm1.clone(), dbm1]).unwrap();

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

        assert!(fed1.eq(&fed1));

        let dbm = DBM::init(4)
            .constrain_and_close(1, 0, LE(5))
            .unwrap()
            .constrain_and_close(0, 1, LE(-5))
            .unwrap();
        let fed2 = OwnedFederation::from_dbms(vec![dbm]).unwrap();

        let res = fed1.clone().subtract(&fed2);

        let res2 = fed1.clone().subtract(&res);

        println!("res1: {res}");
        println!("res2: {res2}");

        assert!(res.eq(&res));
        assert!(res2.eq(&res2));
    }
}
